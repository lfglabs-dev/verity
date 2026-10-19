"""Semantically equivalent variants of the dynamic `T[] calldata` event fixture.

Observable names stay fixed: root functions, events, the custom error and the
parameter types named by the model driver's signatures. Each variant is
imported independently and must reproduce the baseline A/B/C observations.
"""
import re


def stateful_dynamic_address_event_source(original, variant):
    """Equivalent dynamic-array event programs over one transaction sequence."""
    if variant == 'baseline':
        return original
    if variant == 'renamed':
        renamed = original
        for old, new in (('BatchEvents', 'TransferLog'), ('accounts', 'holders'), ('amounts', 'quantities'),
                         ('target', 'receiver'), ('total', 'tally'), ('values', 'bits'), ('keys', 'ids'),
                         ('small', 'bytesSeen'), ('note', 'memo'), ('tag', 'label')):
            renamed = re.sub(rf'\b{old}\b', new, renamed)
        return renamed
    if variant == 'expanded':
        replacements = [
            ('require(accounts.length == amounts.length, InconsistentInput());',
             'if (accounts.length != amounts.length) revert InconsistentInput();'),
            ('total += accounts.length;', 'uint256 added = accounts.length;\n        total = total + added;'),
            ('emit BatchEvents.Batch(target, accounts, amounts, msg.sender);',
             'address origin = target;\n        address sender = msg.sender;\n'
             '        emit BatchEvents.Batch(origin, accounts, amounts, sender);'),
            ('return values.length + keys.length;',
             'uint256 sum = values.length;\n        sum += keys.length;\n        return sum;'),
            ('emit Flags(tag, values, note, keys);',
             'uint64 memo = note;\n        emit Flags(tag, values, memo, keys);'),
        ]
        expanded = original
        for old, new in replacements:
            if expanded.count(old) != 1:
                raise ValueError('nonunique dynamic-event variant anchor')
            expanded = expanded.replace(old, new)
        return expanded
    raise ValueError('unknown dynamic-event program variant')
