"""Exact initial account inputs shared by real-EVM and Denote replay adapters."""
from solidity_differential.engine import HarnessError
from solidity_differential.stateful import _bytes


def canonical_accounts(entries, reserved=()):
    """Validate explicit account inputs; never infer nonce/balance from code."""
    blocked = {_bytes(address, 20) for address in reserved}
    result, seen = [], set()
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {'address', 'code', 'nonce', 'balance'}:
            raise HarnessError('initial account requires exactly address/code/nonce/balance')
        address = _bytes(entry['address'], 20)
        code = _bytes(entry['code'])
        nonce, balance = entry['nonce'], entry['balance']
        if type(nonce) is not int or not 0 <= nonce < 1 << 64:
            raise HarnessError('initial account nonce must fit uint64')
        if type(balance) is not int or not 0 <= balance < 1 << 256:
            raise HarnessError('initial account balance must fit uint256')
        if address in seen:
            raise HarnessError('duplicate initial account')
        if address in blocked:
            raise HarnessError('initial account would overwrite a deployed fixture or sender')
        seen.add(address)
        result.append({'address': address, 'code': code, 'nonce': nonce, 'balance': balance})
    return result


def install_accounts(node, entries, reserved=()):
    """Install the same supplied world used by Denote, then read it back."""
    accounts = canonical_accounts(entries, reserved)
    # Check the whole input before making any changes.
    for account in accounts:
        address = account['address']
        node.rpc('anvil_setCode', address, account['code'])
        node.rpc('anvil_setNonce', address, hex(account['nonce']))
        node.rpc('anvil_setBalance', address, hex(account['balance']))
    for account in accounts:
        address = account['address']
        if (node.rpc('eth_getCode', address, 'latest') != account['code'] or
                int(node.rpc('eth_getTransactionCount', address, 'latest'), 16) != account['nonce'] or
                int(node.rpc('eth_getBalance', address, 'latest'), 16) != account['balance']):
            raise HarnessError('initial account installation changed the supplied world')
    return accounts
