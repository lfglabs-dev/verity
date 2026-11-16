// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

struct Call {
    address target;
    bytes data;
    uint256 tag;
}

/// Solidity reference: the first 32 bytes of the member (zero-padded) and its length.
contract StructBytesMemberCopyRef {
    function copyData(Call calldata c) external pure returns (uint256 w) {
        uint256 n = c.data.length < 32 ? c.data.length : 32;
        for (uint256 i = 0; i < n; i++) {
            w |= uint256(uint8(c.data[i])) << (8 * (31 - i));
        }
    }

    function dataLength(Call calldata c) external pure returns (uint256) {
        return c.data.length;
    }
}

/// The compiled `copyBytes c.data 128` / `bytesLength c.data` on a `(address, bytes, uint256)`
/// struct parameter, against Solidity. A Yul mutant reading the wrong member word shows the
/// comparison has teeth.
contract StructBytesMemberCopySmokeTest is Test, YulTestBase {
    address internal smoke;
    StructBytesMemberCopyRef internal ref;

    string internal constant NAME = "StructBytesMemberCopySmoke";

    function setUp() public {
        smoke = deployCompiledVerityModule("Contracts.Smoke.StructBytesMemberCopySmoke", NAME, _smokeYulDir());
        ref = new StructBytesMemberCopyRef();
    }

    function _bytes(uint256 n) internal pure returns (bytes memory b) {
        b = new bytes(n);
        for (uint256 i = 0; i < n; i++) {
            b[i] = bytes1(uint8(0xa0 + (i % 0x5f)));
        }
    }

    function _call(address who, string memory sig, Call memory c) internal returns (bool ok, uint256 v) {
        bytes memory out;
        (ok, out) = who.call(abi.encodeWithSignature(sig, c));
        if (ok && out.length == 32) v = abi.decode(out, (uint256));
    }

    function _check(address who, Call memory c) internal {
        (bool ok1, uint256 w) = _call(who, "copyData((address,bytes,uint256))", c);
        (bool ok2, uint256 n) = _call(who, "dataLength((address,bytes,uint256))", c);
        assertTrue(ok1 && ok2, "call failed");
        assertEq(w, ref.copyData(c), "copyData");
        assertEq(n, ref.dataLength(c), "dataLength");
    }

    function testLengthsMatchSolidity() public {
        uint256[8] memory lens = [uint256(0), 1, 31, 32, 33, 64, 65, 100];
        for (uint256 i = 0; i < lens.length; i++) {
            _check(smoke, Call(address(0xBEEF), _bytes(lens[i]), 7 + i));
        }
    }

    function testFuzzMatchesSolidity(address target, bytes calldata data, uint256 tag) public {
        _check(smoke, Call(target, data, tag));
    }

    /// Negative control: the same Yul with the member read at head word 2 (`tag`) instead of
    /// word 1 (`data`) disagrees with Solidity.
    function testWrongMemberWordMutantDiffers() public {
        string memory src = vm.readFile(string.concat(_smokeYulDir(), "/", NAME, ".yul"));
        string memory good = "_calldata_checked(c_data_offset, 1)";
        string memory bad = "_calldata_checked(c_data_offset, 2)";
        assertTrue(bytes(vm.replace(src, good, bad)).length > 0);
        assertTrue(keccak256(bytes(vm.replace(src, good, bad))) != keccak256(bytes(src)), "pattern not found");
        string memory dir = "artifacts/struct-bytes-member-mutant";
        vm.createDir(dir, true);
        string memory path = string.concat(dir, "/", NAME, ".yul");
        vm.writeFile(path, vm.replace(src, good, bad));
        address mutant = _deploy(_compileYul(path));

        Call memory c = Call(address(0xBEEF), _bytes(33), 0x40);
        (bool ok1, uint256 w) = _call(mutant, "copyData((address,bytes,uint256))", c);
        (bool ok2, uint256 n) = _call(mutant, "dataLength((address,bytes,uint256))", c);
        assertTrue(!ok1 || !ok2 || w != ref.copyData(c) || n != ref.dataLength(c), "mutant agrees with Solidity");
    }
}
