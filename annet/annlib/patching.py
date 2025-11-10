from __future__ import annotations
from collections.abc import Iterable
import copy
import operator
import re
import string
import sys
import textwrap
from collections import OrderedDict as odict
from typing import (
    Any,
    Callable,
    Iterator,
    Literal,
    TypeAlias,
    TypedDict,
)
if sys.version_info >= (3, 11):
    from typing import NotRequired as NotRequired
else:
    from typing import Union as NotRequired

from .lib import jun_activate, merge_dicts, strip_annotation, uniq
from .rbparser import platform
from .rbparser.ordering import CompiledOrderingAttrs, CompiledOrderingItem, CompiledTree, compile_ordering_text, flatten_order_rb
from .rulebook.common import call_diff_logic
from .rulebook.common import default as common_default
from annet.vendors.tabparser import CommonFormatter
from .types import Diff, Op
from ..vendors import registry_connector


# =====
class AclError(Exception):
    pass


class AclNotExclusiveError(AclError):
    pass


class PatchRow:
    row: str

    def __init__(self, row: str) -> None:
        self.row = row

    def __eq__(self, other: object) -> bool:
        if isinstance(other, str):
            return self.row == other
        if not isinstance(other, PatchRow):
            return NotImplemented
        return self.row == other.row

    def __hash__(self) -> int:
        return hash(self.row)

    def __str__(self) -> str:
        return self.row


class PatchItem:
    row: str
    child: PatchTree | None
    context: dict[str, str]
    sort_key: tuple[Any, ...]

    def __init__(self, row: str, child: PatchTree | None, context: dict[str, str], sort_key: tuple[Any, ...]) -> None:
        self.row = row
        self.child = child
        self.context = context
        self.sort_key = sort_key

    def to_json(self) -> dict[str, Any]:
        return {
            "row": self.row,
            "child": self.child.to_json() if self.child is not None else None,
            "context": self.context,
            "sort_key": self.sort_key,
        }

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> PatchItem:
        return cls(
            row=data["row"],
            child=PatchTree.from_json(data["child"]) if data["child"] is not None else None,
            context=data["context"],
            sort_key=data["sort_key"],
        )

    def __str__(self) -> str:
        return (
            f"PatchItem(\n"
            f"    row={self.row!r},\n"
            f"    child={textwrap.indent(str(self.child), '    ').strip()},\n"
            f"    context={self.context}\n"
            f"    sort_key={self.sort_key}\n"
            f")"
        )


class PatchTree:
    itms: list[PatchItem]

    def __init__(self, row: str | None = None) -> None:
        self.itms = []
        if row:
            self.add(row, {})

    def add(self, row: str, context: dict[str, str], sort_key: tuple[Any, ...] = ()) -> None:
        self.itms.append(PatchItem(row, None, context, sort_key))

    def add_block(self, row: str, subtree: PatchTree | None = None, context: dict[str, str] | None = None, sort_key: tuple[Any, ...] = ()) -> PatchTree:
        if subtree is None:
            subtree = PatchTree()
        if context is None:
            context = {}
        self.itms.append(PatchItem(row, subtree, context, sort_key))
        return subtree

    def items(self) -> Iterator[tuple[str, PatchTree | None]]:
        for item in self.itms:
            yield str(item.row), item.child

    def asdict(self) -> odict[str, Any]:
        ret = odict()
        for row in uniq(i.row for i in self.itms):
            subtrees = []
            for i in self.itms:
                if i.row == row and i.child is not None:
                    subtrees.append(i.child.asdict())
            if subtrees:
                ret[str(row)] = merge_dicts(*subtrees)
            else:
                ret[str(row)] = None
        return ret

    def to_json(self) -> list[dict[str, Any]]:
        return [i.to_json() for i in self.itms]

    @classmethod
    def from_json(cls, data: list[dict[str, Any]]) -> PatchTree:
        ret = cls()
        ret.itms = [PatchItem.from_json(i) for i in data]
        return ret

    def sort(self) -> None:
        self.itms.sort(key=operator.attrgetter("sort_key"))
        for item in self.itms:
            if item.child is not None:
                item.child.sort()

    def __bool__(self) -> bool:
        return bool(self.itms)

    def __str__(self) -> str:
        n = ",\n"
        itms = map(lambda x: textwrap.indent(str(x), "    "), self.itms)
        return (
            f"PatchTree(\n"
            f"    itms=[\n"
            f"{textwrap.indent(n.join(itms), '    ')}\n"
            f"    ]\n"
            f")"
        )


def string_similarity(s: str, pattern: str) -> float:
    """
    >>> string_similarity("abc", "ab")
    0.6666666666666666
    >>> string_similarity("aabb", "ab")
    0.5
    >>> string_similarity("aabb", "x")
    0.0
    >>> string_similarity("a", "ab")
    1.0
    """
    return len(set(s) & set(pattern)) / len(s)

def rule_weight(row: str, rule: CompiledOrderingItem, regexp_key: Literal["direct_regexp", "reverse_regexp"]) -> float:
    return string_similarity(row, rule["attrs"][regexp_key].pattern)

SortKey: TypeAlias = tuple[tuple[tuple[float, tuple[str, ...]], ...], bool]

class Orderer:
    def __init__(self, rb: CompiledTree, vendor: str) -> None:
        self.rb = rb
        self.vendor = vendor

    def ref_insert(self, ref_tracker):
        for ref, _ in reversed(ref_tracker.configs()):
            self.insert(ref)
        for _, defs in reversed(ref_tracker.configs()):
            self.insert(defs)

    def insert(self, rules: PatchTree) -> None:
        if isinstance(rules, dict):
            fmtr = CommonFormatter()
            rules = fmtr.join(rules)
        rb = compile_ordering_text(rules, self.vendor)
        self.rb = self.rb + rb

    def get_order(
        self,
        row: tuple[str, ...],
        cmd_direct: bool,
        keys: tuple[tuple[str, ...], ...] = (),
        scope: str | None = None,
    ) -> SortKey:
        block_exit = registry_connector.get()[self.vendor].exit

        from itertools import zip_longest

        vectors: list[tuple[list[float], SortKey]] = []
        rulebook_rows = [*flatten_order_rb(self.rb)]

        for rb_row in rulebook_rows:
            vector: list[tuple[float, tuple[str, ...]]] = []
            weight: list[float] = []
            matched = True
            global_rules = None
            for i, (rb_item, row_item, key) in enumerate(zip_longest(rb_row, row, keys, fillvalue=None)):
                weight.append(0.)
                if key is None:
                    key = ()

                if rb_item is None:
                    weight[-1] -= 1e-6
                    vector.append((0, key))
                    continue

                if row_item is None:
                    matched = False
                    break

                rb_idx, _, rb_attrs, global_rules = rb_item
                if (
                    (rule_scope := rb_attrs["scope"]) is not None
                    and scope not in rule_scope
                ):
                    matched = False
                    break
                rb_idx += 1  # so that negated index is always smaller

                direct_matched = bool(rb_attrs["direct_regexp"].match(row_item))
                reverse_matched = bool(rb_attrs["reverse_regexp"].match(row_item))
                order_reverse = rb_attrs["order_reverse"]

                if not order_reverse and direct_matched:
                    weight[-1] += string_similarity(row_item, rb_attrs["direct_regexp"].pattern)
                    vector.append((rb_idx * (+1 if cmd_direct or i != len(row) - 1 else -1), key))

                elif not order_reverse and reverse_matched:
                    weight[-1] += string_similarity(row_item, rb_attrs["reverse_regexp"].pattern) * 0.5
                    vector.append((rb_idx * (+1 if cmd_direct else -1), key))

                elif order_reverse and not cmd_direct and direct_matched:
                    weight[-1] += string_similarity(row_item, rb_attrs["direct_regexp"].pattern)
                    vector.append((+rb_idx, key))

                elif block_exit and block_exit == row_item:
                    vector.append((float('inf'), ()))
                    matched = True
                    break

                else:
                    matched = False
                    break

            if matched:
                vectors.append((weight, (tuple(vector), cmd_direct)))

                assert global_rules is not None
                for gl_rule in global_rules:
                    rulebook_rows.append(rb_row + ((gl_rule[0], '<unused>', gl_rule[1]["attrs"], global_rules),))

        if not vectors:
            return (((0, ()),), cmd_direct)

        vectors.sort(key=lambda x: (
            -len(x[1][0]), # most precise position
            [-w for w in x[0]], # biggest weight
            x[1], # the first one
        ))
        return vectors[0][1]

    def order_config(self, config: dict[str, Any], _path: tuple[str, ...] = ()) -> dict[str, Any]:
        if self.vendor not in registry_connector.get():
            return config
        if not config:
            return odict()

        ret: dict[str, Any] = {}
        sort_keys: dict[str, SortKey] = {}

        reverse_prefix = registry_connector.get()[self.vendor].reverse
        for row, children in config.items():
            cmd_direct = not row.startswith(reverse_prefix)

            sort_key = self.get_order(_path + (row,), cmd_direct=cmd_direct)
            children = self.order_config(children, _path=(*_path, row))
            ret[row] = children
            sort_keys[row] = sort_key

        return odict(
            (row, children)
            for row, children in sorted(ret.items(), key=lambda kv: sort_keys[kv[0]])
        )



# =====
def apply_acl(config, rules, fatal_acl=False, exclusive=False, with_annotations=False, _path=()):
    passed = odict()
    for (row, children) in config.items():
        if with_annotations:
            # do not pass annotations through ACL
            test_row = strip_annotation(row)
        else:
            test_row = row
        try:
            (match, children_rules) = match_row_to_acl(test_row, rules, exclusive)
        except AclNotExclusiveError as err:
            raise AclNotExclusiveError("'%s', %s" % ("/ ".join(_path + (row,)), err))
        if match:
            if not (match["is_reverse"] and all(match["attrs"]["cant_delete"])):
                passed[row] = apply_acl(
                    config=children,
                    rules=children_rules,
                    fatal_acl=fatal_acl,
                    exclusive=exclusive,
                    with_annotations=with_annotations,
                    _path=_path + (row,)
                )
        elif fatal_acl:
            raise AclError(" / ".join(_path + (row,)))
    return passed


def apply_acl_diff(diff, rules):
    passed = []
    for (op, row, children, d_match) in diff:
        (match, children_rules) = match_row_to_acl(row, rules)
        if match:
            if op == Op.REMOVED and all(match["attrs"]["cant_delete"]):
                op = Op.AFFECTED
            children = apply_acl_diff(children, children_rules)
            passed.append((op, row, children, d_match))
    return passed


def mark_unchanged(diff):
    passed = []
    for (op, row, children, d_match) in diff:
        if op == Op.AFFECTED:
            children = mark_unchanged(children)
            if all(x[0] == Op.UNCHANGED for x in children):
                op = Op.UNCHANGED
        passed.append((op, row, children, d_match))
    return passed


def strip_unchanged(diff):
    passed = []
    for (op, row, children, d_match) in diff:
        if op == Op.UNCHANGED:
            continue
        children = strip_unchanged(children)
        passed.append((op, row, children, d_match))
    return passed


def make_diff(old, new, rb, acl_rules_list) -> Diff:
    # не позволяем logic-коду модифицировать конфиг
    old = copy.deepcopy(old)
    new = copy.deepcopy(new)
    diff_pre = apply_diff_rb(old, new, rb)
    diff = call_diff_logic(diff_pre, old, new)
    for acl_rules in acl_rules_list:
        if acl_rules is not None:
            diff = apply_acl_diff(diff, acl_rules)
    diff = mark_unchanged(diff)
    return diff


def apply_diff_rb(old, new, rb):
    """ Diff pre is a odict {(key, diff_logic): {}} """
    diff_pre = odict()
    for row in list(uniq(old, new)):
        (match, children_rules) = _match_row_to_rules(row, rb["patching"])
        if match:
            diff_pre[row] = {
                "match": match,
                "subtree": apply_diff_rb(
                    old.get(row, odict()),
                    new.get(row, odict()),
                    rb={"patching": children_rules},  # Нужен только кусок, касающийся правил для патчей
                ),
            }
        else:
            old.pop(row, None)
            new.pop(row, None)
    return diff_pre


def make_pre(diff: Diff, _parent_match=None) -> dict[str, Any]:
    pre = odict()
    for (op, row, children, match) in diff:
        if _parent_match and _parent_match["attrs"]["multiline"]:
            # Если родительское правило было мультилайном, то все внутренности станут его контентом.
            # Это значит, что к ним будет принудительно применяться common.default() и фейковое
            # правило __MULTILINE_BODY__.
            match = {
                "raw_rule": "__MULTILINE_BODY__",
                "key": row,
                "attrs": {
                    "comment": [],
                    "logic": common_default,  # Прекрасно работает с мультилайнами и обрезанным правилом
                    "multiline": True,
                    "context": _parent_match["attrs"]["context"],
                }
            }
        raw_rule = match["raw_rule"]
        key = match["key"]

        if raw_rule not in pre:
            pre[raw_rule] = {
                "attrs": match["attrs"],
                "items": odict(),
            }
        if key not in pre[raw_rule]["items"]:
            pre[raw_rule]["items"][key] = {
                Op.ADDED: [],
                Op.REMOVED: [],
                Op.MOVED: [],
                Op.AFFECTED: [],
                Op.UNCHANGED: [],
            }

        pre[raw_rule]["items"][key][op].append({
            "row": row,
            "children": make_pre(
                diff=children,
                _parent_match=match,
            ),
        })
    return pre


_comment_macros = {
    "!!HYES!!": "!!question!![Y/N]!!answer!!Y!! !!question!![y/n]!!answer!!Y!! !!question!![Yes/All/No/Cancel]!!answer!!Y!!"
}

class _PreAttrs(TypedDict):
    logic: Callable[..., Iterable[tuple[bool | None, str, odict[str, _Content] | None]]]
    diff_logic: Callable
    regexp: re.Pattern[str]
    reverse: str
    comment: list[str]
    multiline: bool
    parent: NotRequired[bool]
    force_commit: bool
    ignore_case: bool
    context: Any

class _DiffItem(TypedDict):
    row: str
    children: odict[str, _Content]

class _Content(TypedDict):
    attrs: _PreAttrs
    items: odict[tuple[str, ...], dict[Op, list[_DiffItem]]]

class _PatchRow(TypedDict):
    row: tuple[str, ...]
    keys: tuple[tuple[str, ...], ...]
    attrs: _PreAttrs
    direct: bool
    rules: tuple[str, ...]
    block: bool

def _iterate_over_patch(
    pre: odict[str, _Content],
    hw,
    do_commit: bool,
    add_comments: bool,
    _root_pre: odict[str, _Content] | None = None,
) -> Iterable[_PatchRow]:
    for raw_rule, content in pre.items():
        for key, diff in content["items"].items():
            rule_pre = content.copy()
            attrs = copy.deepcopy(rule_pre["attrs"])
            iterable = attrs["logic"](
                rule=attrs,
                key=key,
                diff=diff,
                hw=hw,
                rule_pre=rule_pre,
                root_pre=(_root_pre or pre),
            )
            for (direct, row, sub_pre) in iterable:
                if direct is None:
                    continue

                if add_comments:
                    comments = " ".join(attrs["comment"])
                    for (macro, m_value) in _comment_macros.items():
                        comments = comments.replace(macro, m_value)
                    if comments:
                        row = f"{row} {comments}"

                if not do_commit and attrs.get("force_commit", False):
                    # if do_commit is false skip patch that couldn't be applied without commit
                    continue

                if not sub_pre:
                    yield _PatchRow(
                        row=(row,),
                        keys=(key,),
                        attrs=attrs.copy(),
                        direct=direct,
                        rules=(raw_rule,),
                        block=False,
                    )

                else:
                    for sub_row in _iterate_over_patch(
                        sub_pre,
                        hw=hw,
                        add_comments=add_comments,
                        do_commit=do_commit,
                        _root_pre=(_root_pre or pre),
                    ):
                        new_rules: list[str] = [raw_rule]
                        for rule in sub_row["rules"]:
                            if rule != new_rules[-1]:
                                new_rules.append(rule)
                        yield _PatchRow(
                            row=(row, *sub_row["row"]),
                            keys=(key, *sub_row["keys"]),
                            attrs=sub_row["attrs"],
                            direct=sub_row["direct"],
                            rules=tuple(new_rules),
                            block=sub_row["block"],
                        )

def sort_patch_rows(orderer: Orderer, patch_rows: list[_PatchRow]) -> list[_PatchRow]:
    sort_keys = []
    string_idxs: dict[tuple[tuple[str, ...], ...], int] = {}
    for i, row in enumerate(patch_rows):
        orderer_pos, direct = orderer.get_order(row["row"], keys=row["keys"],cmd_direct=row["direct"], scope="patch")
        keys = tuple(key for _, key in orderer_pos)
        for prefix_size in range(len(keys) + 1):
            prefix = keys[:prefix_size]
            if prefix not in string_idxs:
                string_idxs[prefix] = i

        sort_key: list[tuple[float, int]] = []
        for j, (idx, _) in enumerate(orderer_pos):
            sort_key.append((
                idx,
                row["rules"][j] if j < len(row["rules"]) else "",
                True if j != len(orderer_pos) - 1 else row["direct"],
                string_idxs[keys[:j+1]],
            ))

        sort_keys.append((sort_key, direct, keys))

    patch_rows__idxs = [(row, i) for i, row in enumerate(patch_rows)]
    patch_rows__idxs.sort(key=lambda row_idx: sort_keys[row_idx[1]])

    return [row for row, _ in patch_rows__idxs]

def make_patch(
    pre: odict[str, _Content],
    rb: dict[str, CompiledTree],  # not correct, but good enough for now; TODO: make typeddict for this
    hw,
    add_comments: bool,
    orderer: Orderer | None = None,
    _root_pre: odict[str, _Content] | None = None,
    do_commit: bool = True,
) -> PatchTree:
    if not orderer:
        orderer = Orderer(rb["ordering"], hw.vendor)

    patch_rows = list(_iterate_over_patch(
        pre,
        hw,
        add_comments=add_comments,
        do_commit=do_commit,
        _root_pre=(_root_pre or pre),
    ))
    patch_rows = sort_patch_rows(orderer, patch_rows)

    tree = PatchTree()
    for patch_row in patch_rows:
        node = tree
        for i, x in enumerate(patch_row["row"]):
            if not node.itms or node.itms[-1].row != x:
                if not patch_row["block"] and not patch_row["attrs"].get("parent", False) or not patch_row["direct"]:
                    subtree = None
                else:
                    subtree = PatchTree()
                node.itms.append(PatchItem(x, subtree, patch_row["attrs"]["context"], ...))

                if patch_row["attrs"].get("force_commit", False):
                    node.itms.append(PatchItem("commit", None, patch_row["attrs"]["context"], ...))

            if i != len(patch_row["row"]) - 1:
                if node.itms[-1].child is None:
                    node.itms[-1].child = PatchTree()
                node = node.itms[-1].child

    return tree

def match_row_to_acl(row, rules, exclusive=False):
    matches = _find_acl_matches(row, rules)
    if matches:
        if exclusive:
            gen_cant_delete = {}
            for match in matches:
                names = match[0][0]["attrs"]["generator_names"]
                flags = match[0][0]["attrs"]["cant_delete"]
                for name, flag in zip(names, flags):
                    if name not in gen_cant_delete:
                        gen_cant_delete[name] = flag
                    else:
                        gen_cant_delete[name] &= flag
            can_delete = {name: flag for name, flag in gen_cant_delete.items() if not flag}
            if len(can_delete) > 1:
                generator_names = ", ".join(can_delete.keys())
                raise AclNotExclusiveError("generators: '%s'" % generator_names)
        return _select_match(matches, rules)
    return (None, None)  # (match, children_rules)


def _match_row_to_rules(row, rules):
    matches = _find_rules_matches(row, rules)
    if matches:
        return _select_match(matches, rules)
    return (None, None)


def _find_acl_matches(row, rules):
    res = []
    for regexp_key in ["direct_regexp", "reverse_regexp"]:
        for ((_, rule), is_global) in _rules_local_global(rules):
            row_to_match = _normalize_row_for_acl(row, rule)
            match = rule["attrs"][regexp_key].match(row_to_match)
            if match:
                rule["attrs"]["match"] = match.groupdict()
                # FIXME: сейчас у нас вообще не используется тип ignore, но он иногда встречается в ACL.
                # Проблема в том, что ACL мержится, и игноры все ломают. Надо придумать, что с этим сделать.
                # В данный момент ignore acl работает только в filter-acl, так как он целостный и накладывается независимо
                # В этом случае ignore правила так же матчатся и считается их специфичность на ряду с normal
                # при выборе ignore правила, заматченная строка не будет пропущена
                metric = (
                    rule["attrs"]["prio"],
                    # Calculate how specific matched regex is for the row
                    # based on how many symbols they share
                    rule_weight(row, rule, regexp_key)
                )
                item = (
                    metric,
                    ((rule, (not is_global and regexp_key == "direct_regexp" and rule["type"] != "ignore")),
                     #       ^^^ is_cr_allowed ^^^    cr == children rules
                     {"is_reverse": (regexp_key == "reverse_regexp")}),
                    # ^^^ is_reverse ^^^
                )
                res.append(item)
    res.sort(key=operator.itemgetter(0), reverse=True)
    return [item[1] for item in res]


def _find_rules_matches(row, rules):
    matches = []
    for ((raw_rule, rule), is_global) in _rules_local_global(rules):
        match = rule["attrs"]["regexp"].match(row)
        if match:
            if rule["type"] == "ignore":
                return []
            matches.append(((rule, (not is_global)), {"raw_rule": raw_rule, "key": match.groups()}))
            #                       ^^^ is_cr_allowed
    return matches


def _select_match(matches, rules):
    ((f_rule, is_f_cr_allowed), f_other) = matches[0]  # f == first
    if f_rule["type"] == "ignore":
        # В данный момент эта ветка достижима только в filter-acl
        return (None, None)

    # Мерджим всех потомков которые заматчились
    local_children = odict()
    global_children = odict()
    if is_f_cr_allowed:
        for (rule, is_cr_allowed) in map(operator.itemgetter(0), matches):
            if is_cr_allowed:
                local_children = merge_dicts(local_children, rule["children"]["local"])
                # optional break on is_cr_allowed==False?
                global_children = merge_dicts(global_children, rule["children"]["global"])

    global_children = merge_dicts(global_children, rules["global"])

    children_rules = {
        "local": local_children,
        "global": global_children,
    }

    match = {"attrs": copy.deepcopy(f_rule["attrs"])}
    match.update(f_other)

    return match, children_rules


def _rules_local_global(rules):
    for (raw_rule, rule) in rules["local"].items():
        yield ((raw_rule, rule), False)
    for (raw_rule, rule) in rules["global"].items():
        yield ((raw_rule, rule), True)


def _normalize_row_for_acl(row, rule):
    # NOCDEV-5940 У джуниперов есть служебрая разметка "inactive:"
    if rule["attrs"]["vendor"] == "juniper":
        row = jun_activate(row)
    return row
