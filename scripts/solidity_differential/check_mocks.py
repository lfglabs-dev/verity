"""Execute each configured external-world behavior in real Anvil transactions."""
from pathlib import Path
import tempfile
from eth_abi import encode
from eth_hash.auto import keccak

from .anvil import Anvil
from .engine import solc_compile, write_json


def main():
    output = Path(tempfile.mkdtemp(prefix='stateful-mocks-', dir='.lake')).resolve()
    fixture = Path(__file__).parent / 'fixtures/Mocks.sol'
    compiled = solc_compile({'language': 'Solidity', 'sources': {'Mocks.sol': {'content': fixture.read_text()}},
        'settings': {'evmVersion': 'osaka', 'viaIR': True, 'optimizer': {'enabled': True, 'runs': 466},
        'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}, fixture.parent, output / 'solc')
    contracts = compiled['contracts']['Mocks.sol']
    observations = []
    with Anvil(output) as node:
        sender, recipient = node.rpc('eth_accounts')[:2]
        def deploy(name):
            result = node.transact({'from': sender, 'data': '0x' + contracts[name]['evm']['bytecode']['object'], 'gas': hex(4000000)})
            assert result['receipt']['status'] == '0x1'
            return result['receipt']['contractAddress']
        def calldata(name, signature, types=(), args=()):
            return '0x' + contracts[name]['evm']['methodIdentifiers'][signature] + encode(types, args).hex()
        def call(name, target, signature, types=(), args=()):
            result = node.transact({'from': sender, 'to': target, 'gas': hex(2000000), 'data': calldata(name, signature, types, args)})
            observed = node.observe(result, str(len(observations)))
            observations.append(observed)
            return observed
        zero = '0x' + '00' * 20
        def balance(token, owner):
            return int(call('TokenMock', token, 'balanceOf(address)', ['address'], [owner])['data'], 16)
        for mode in range(4):
            token = deploy('TokenMock')
            call('TokenMock', token, 'configure(uint8,uint256,address,bytes)', ['uint8','uint256','address','bytes'], [mode,1000,zero,b''])
            call('TokenMock', token, 'mint(address,uint256)', ['address','uint256'], [sender,1000])
            result = call('TokenMock', token, 'transfer(address,uint256)', ['address','uint256'], [recipient,100])
            assert balance(token, sender) == (900 if mode < 2 else 1000)
            assert balance(token, recipient) == (100 if mode == 0 else 90 if mode == 1 else 0)
            assert len(result['events']) == (1 if mode == 0 else 2 if mode == 1 else 0)
            if mode == 3:
                assert result['status'] == 'revert' and result['data'] == '0x' + keccak(b'TransferRejected()')[:4].hex()
            else:
                assert result['status'] == 'ok' and int(result['data'],16) == (0 if mode == 2 else 1)
            call('TokenMock', token, 'approve(address,uint256)', ['address','uint256'], [sender,50])
            delegated = call('TokenMock', token, 'transferFrom(address,address,uint256)',
                             ['address','address','uint256'], [sender,recipient,20])
            permitted = call('TokenMock', token, 'allowance(address,address)', ['address','address'], [sender,sender])
            assert int(permitted['data'],16) == (30 if mode < 2 else 50)
            assert balance(token, sender) == (880 if mode < 2 else 1000)
            assert balance(token, recipient) == (120 if mode == 0 else 108 if mode == 1 else 0)
            assert delegated['status'] == ('revert' if mode == 3 else 'ok')
            call('TokenMock', token, 'approve(address,uint256)', ['address','uint256'], [sender,2**256-1])
            call('TokenMock', token, 'transferFrom(address,address,uint256)',
                 ['address','address','uint256'], [sender,recipient,1])
            permitted = call('TokenMock', token, 'allowance(address,address)', ['address','address'], [sender,sender])
            assert int(permitted['data'],16) == 2**256-1
        oracle = deploy('OracleMock')
        call('OracleMock', oracle, 'configure(uint256,bool)', ['uint256','bool'], [42,False])
        assert int(call('OracleMock', oracle, 'price()')['data'],16) == 42
        call('OracleMock', oracle, 'configure(uint256,bool)', ['uint256','bool'], [42,True])
        assert call('OracleMock', oracle, 'price()')['data'] == '0x' + keccak(b'OracleRejected()')[:4].hex()
        token, callback = deploy('TokenMock'), deploy('CallbackMock')
        for owner in (sender, callback):
            call('TokenMock', token, 'mint(address,uint256)', ['address','uint256'], [owner,100])
        inner = bytes.fromhex(calldata('TokenMock','transfer(address,uint256)', ['address','uint256'], [recipient,5])[2:])
        call('CallbackMock',callback,'configure(address,bytes,bool)', ['address','bytes','bool'],[token,inner,True])
        invoke = bytes.fromhex(calldata('CallbackMock','invoke()')[2:])
        call('TokenMock',token,'configure(uint8,uint256,address,bytes)', ['uint8','uint256','address','bytes'],[0,0,callback,invoke])
        call('TokenMock',token,'transfer(address,uint256)', ['address','uint256'],[recipient,10])
        assert balance(token,recipient) == 15 and balance(token,callback) == 95
        assert int(call('CallbackMock',callback,'calls()')['data'],16) == 1
        price = bytes.fromhex(calldata('OracleMock','price()')[2:])
        call('CallbackMock',callback,'configure(address,bytes,bool)', ['address','bytes','bool'],[oracle,price,True])
        failed = call('TokenMock',token,'transfer(address,uint256)', ['address','uint256'],[recipient,10])
        assert failed['status'] == 'revert' and not failed['events']
        assert failed['data'] == '0x' + keccak(b'OracleRejected()')[:4].hex()
        assert balance(token,recipient) == 15 and balance(token,sender) == 90
        assert int(call('CallbackMock',callback,'calls()')['data'],16) == 1
        call('CallbackMock',callback,'configure(address,bytes,bool)', ['address','bytes','bool'],[oracle,price,False])
        caught = call('TokenMock',token,'transfer(address,uint256)', ['address','uint256'],[recipient,10])
        assert caught['status'] == 'ok' and len(caught['events']) == 1
        assert balance(token,recipient) == 25 and balance(token,sender) == 80
        assert int(call('CallbackMock',callback,'calls()')['data'],16) == 2
        assert int(call('CallbackMock',callback,'lastSuccess()')['data'],16) == 0
    write_json(output / 'observations.json', observations)
    print('Anvil mocks: four token modes, oracle success/revert, reentry and callback rollback passed')


if __name__ == '__main__':
    main()
