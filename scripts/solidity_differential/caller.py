"""Exact caller metadata from an owned node's deployment receipt, never inferred."""
from solidity_differential.accounts import canonical_accounts
from solidity_differential.engine import HarnessError
from solidity_differential.stateful import _bytes


def canonical_caller(entry, target, senders=()):
    caller = canonical_accounts([entry], senders)[0]
    if caller['address'] != _bytes(target, 20):
        raise HarnessError('caller account address differs from model target')
    return caller


def capture_caller(node, receipt):
    if not isinstance(receipt, dict) or receipt.get('status') != '0x1':
        raise HarnessError('caller metadata requires a successful deployment receipt')
    address = _bytes(receipt.get('contractAddress'), 20)
    block = receipt.get('blockNumber')
    actual = node.rpc('eth_getBlockByNumber', block, False)
    if actual.get('hash') != receipt.get('blockHash'):
        raise HarnessError('caller deployment block identity changed')
    # All reads use the same mined deployment block, never a later post-call world.
    caller = canonical_caller({
        'address': address, 'code': node.rpc('eth_getCode', address, block),
        'nonce': int(node.rpc('eth_getTransactionCount', address, block), 16),
        'balance': int(node.rpc('eth_getBalance', address, block), 16)}, address)
    return {'account': caller, 'blockNumber': block, 'blockHash': receipt['blockHash'],
            'transactionHash': receipt['transactionHash']}


def caller_json(entry):
    caller = canonical_accounts([entry])[0]
    return {'address': str(int(caller['address'], 16)), 'nonce': str(caller['nonce']),
            'balance': str(caller['balance']),
            'code': [str(byte) for byte in bytes.fromhex(caller['code'][2:])]}
