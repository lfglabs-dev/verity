// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Solidity twin of `Contracts.Smoke.EventCompositeLiteralSmoke`: the same events, built from the
/// same words, with solc's casts doing the narrowing the Verity encoder does by masking.
contract EventCompositeLiteralSmokeReference {
    struct Cut {
        address target;
        uint8 action;
        bytes4[] selectors;
    }

    event Cuts(Cut[] cuts, address init, bytes data);
    event Pair(uint256 left, uint256[] values, uint256 right);

    function _sel(uint256 word) private pure returns (bytes4) {
        return bytes4(bytes32(word));
    }

    function cutOne(uint256 target, uint256 action, uint256 sel) external {
        Cut[] memory cuts = new Cut[](1);
        bytes4[] memory sels = new bytes4[](1);
        sels[0] = _sel(sel);
        cuts[0] = Cut(address(uint160(target)), uint8(action), sels);
        emit Cuts(cuts, address(0), "");
    }

    function cutTwo(uint256 a, uint256 b, uint256 s0, uint256 s1, uint256 s2, uint256 s3, address init)
        external
    {
        Cut[] memory cuts = new Cut[](2);
        bytes4[] memory first = new bytes4[](1);
        first[0] = _sel(s0);
        bytes4[] memory second = new bytes4[](3);
        second[0] = _sel(s1);
        second[1] = _sel(s2);
        second[2] = _sel(s3);
        cuts[0] = Cut(address(uint160(a)), 0, first);
        cuts[1] = Cut(address(uint160(b)), 2, second);
        emit Cuts(cuts, init, "");
    }

    function pair(uint256 x, uint256 y, uint256 z) external {
        uint256[] memory values = new uint256[](3);
        values[0] = y;
        values[1] = z;
        unchecked {
            values[2] = y + z;
        }
        emit Pair(x, values, z);
    }
}

/// Every `emit` with ABI literal arguments logs exactly the bytes solc logs for the same values:
/// topics and data, for fuzzed (also dirty) leaves.
contract EventCompositeLiteralSmokeTest is Test, YulTestBase {
    address internal smoke;
    EventCompositeLiteralSmokeReference internal referenceContract;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.EventCompositeLiteralSmoke", "EventCompositeLiteralSmoke", _smokeYulDir()
        );
        referenceContract = new EventCompositeLiteralSmokeReference();
    }

    function _recordLogs(address target, bytes memory callData) internal returns (Vm.Log[] memory logs) {
        vm.recordLogs();
        (bool ok,) = target.call(callData);
        assertTrue(ok, "event emitter call failed");
        logs = vm.getRecordedLogs();
    }

    function _assertSameLogs(bytes memory callData) internal {
        Vm.Log[] memory verity = _recordLogs(smoke, callData);
        Vm.Log[] memory solc = _recordLogs(address(referenceContract), callData);
        assertEq(verity.length, 1, "Verity log count");
        assertEq(solc.length, 1, "solc log count");
        assertEq(verity[0].topics.length, solc[0].topics.length, "topic count");
        for (uint256 j = 0; j < solc[0].topics.length; j++) {
            assertEq(verity[0].topics[j], solc[0].topics[j], "topic");
        }
        assertEq(verity[0].data, solc[0].data, "data");
    }

    function testFuzzCutOneMatchesSolc(uint256 target, uint256 action, uint256 sel) public {
        _assertSameLogs(abi.encodeWithSignature("cutOne(uint256,uint256,uint256)", target, action, sel));
    }

    function testFuzzCutTwoMatchesSolc(
        uint256 a,
        uint256 b,
        uint256 s0,
        uint256 s1,
        uint256 s2,
        uint256 s3,
        address init
    ) public {
        _assertSameLogs(
            abi.encodeWithSignature(
                "cutTwo(uint256,uint256,uint256,uint256,uint256,uint256,address)", a, b, s0, s1, s2, s3, init
            )
        );
    }

    function testFuzzPairMatchesSolc(uint256 x, uint256 y, uint256 z) public {
        _assertSameLogs(abi.encodeWithSignature("pair(uint256,uint256,uint256)", x, y, z));
    }

    /// A known vector, so a change in both encoders at once cannot pass unnoticed.
    function testCutOneKnownEncoding() public {
        Vm.Log[] memory logs = _recordLogs(
            smoke, abi.encodeWithSignature("cutOne(uint256,uint256,uint256)", uint256(0xaa), uint256(1), uint256(0x11223344) << 224)
        );
        assertEq(logs[0].topics[0], keccak256("Cuts((address,uint8,bytes4[])[],address,bytes)"));
        assertEq(
            logs[0].data,
            abi.encode(
                uint256(0x60), uint256(0), uint256(0x140), // heads: cuts, init, data
                uint256(1), uint256(0x20), // one cut, at offset 0x20
                uint256(0xaa), uint256(1), uint256(0x60), // target, action, selectors offset
                uint256(1), uint256(0x11223344) << 224, // one selector
                uint256(0) // empty bytes
            )
        );
    }
}
