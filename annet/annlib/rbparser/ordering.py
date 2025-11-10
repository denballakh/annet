from __future__ import annotations
from collections.abc import Iterator
import functools
import re
from collections import OrderedDict as odict

from valkit.common import valid_bool, valid_string_list

from annet.vendors import registry_connector
from . import syntax

from typing import TypedDict, Any

# =====
# 'global' is a keyword, so we cant use normal TypedDict declaration
CompiledOrderingAttrs = TypedDict("CompiledOrderingAttrs", {
    "direct_regexp": re.Pattern[str],
    "reverse_regexp": re.Pattern[str],
    "order_reverse": bool,
    "global": bool,  # TODO: rename to something else so that it is not a keyword
    "scope": list[str] | None,
    "raw_rule": str,
    "context": Any,
})

class CompiledOrderingItem(TypedDict):
    attrs: CompiledOrderingAttrs
    children: CompiledTree

CompiledTree = list[tuple[str, CompiledOrderingItem]]


@functools.lru_cache()
def compile_ordering_text(text: str, vendor: str):
    return _compile_ordering(
        tree=syntax.parse_text_multi(text, params_scheme={
            "order_reverse": {
                "validator": valid_bool,
                "default":   False,
            },
            "global": {
                "validator": valid_bool,
                "default": False,
            },
            "scope": {
                "validator": valid_string_list,
                "default": None,
            }
        }),
        reverse_prefix=registry_connector.get()[vendor].reverse,
    )


def decompile_ordering_rulebook(rb) -> str: # FIXME
    def _decompile_ordering_text(rb, level):
        indent = "  "
        for attrs in rb.values():
            yield indent * level + attrs["attrs"]["raw_rule"]
            yield from _decompile_ordering_text(attrs["children"], level + 1)
    return "\n".join(_decompile_ordering_text(rb, 0))


# =====


def flatten_order_rb(rb: CompiledTree, global_rules: list[tuple[int, CompiledOrderingItem]] = []) -> Iterator[tuple[tuple[int, str, CompiledOrderingAttrs, list[tuple[int, CompiledOrderingItem]]], ...]]:
    new_global_rules = global_rules[:]

    for i, (raw_rule, rule) in enumerate(rb):
        if rule["attrs"]["global"]:
            new_global_rules.append((i, rule))

    for i, (raw_rule, rule) in enumerate(rb):
        if rule["children"]:
            for x in flatten_order_rb(rule["children"], new_global_rules):
                yield ((i, raw_rule, rule["attrs"], new_global_rules), *x)

        yield ((i, raw_rule, rule["attrs"], new_global_rules),)

def _compile_ordering(tree: syntax.ParsedTree, reverse_prefix: str) -> CompiledTree:
    ordering: CompiledTree = []
    for (rule_id, attrs) in tree:
        if attrs["type"] == "normal":
            ordering.append((
                rule_id,
                {
                "attrs": CompiledOrderingAttrs({
                    "direct_regexp": syntax.compile_row_regexp(attrs["row"]),
                    "reverse_regexp": (
                        syntax.compile_row_regexp(reverse_prefix + " " + attrs["row"])
                        if not attrs["row"].startswith(reverse_prefix + " ") else
                        syntax.compile_row_regexp(re.sub(r"^%s\s+" % (reverse_prefix), "", attrs["row"]))
                    ),
                    "order_reverse": attrs["params"]["order_reverse"],
                    "global": attrs["params"]["global"],
                    "scope": attrs["params"]["scope"],
                    "raw_rule": attrs["raw_rule"],
                    "context": attrs["context"],
                }),
                "children": _compile_ordering(attrs["children"], reverse_prefix),
            }))
    return ordering
