// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (c) 2026 Morpho Association
pragma solidity ^0.8.0;

import {Market} from "../interfaces/IMidnight.sol";

library IdLib {
    error SStore2DeploymentFailed();

    /// @dev Used as a prefix to some data, to give a creation code that deploys the data as runtime bytecode.
    /// @dev Explanation of the prefix:
    /// hex       opcode          stack              comments
    /// ------------------------------------------------------------------------------
    /// 60 0b     PUSH1 0x0b      [11]               11 = length(prefix)
    /// 38        CODESIZE        [codesize, 11]
    /// 03        SUB             [len]              with len = codesize - 11
    /// 80        DUP1            [len, len]
    /// 60 0b     PUSH1 0x0b      [11, len, len]     code offset = 11
    /// 5f        PUSH0           [0, 11, len, len]  mem offset = 0
    /// 39        CODECOPY        [len]              mem[0:len] <- code[11:11+len]
    /// 5f        PUSH0           [0, len]           return offset = 0
    /// f3        RETURN          []                 mem[0:len] is returned
    bytes constant SSTORE2_PREFIX = hex"600b380380600b5f395ff3";

    function toId(Market memory market) internal pure returns (bytes32) {
        // forge-lint: disable-next-item(encode-packed-collision) there is no ambiguity since SSTORE2_PREFIX has a fixed size.
        return keccak256(
            abi.encodePacked(
                uint8(0xff),
                market.midnight,
                uint256(0),
                keccak256(abi.encodePacked(SSTORE2_PREFIX, abi.encode(market)))
            )
        );
    }

    /// @dev Stores the market in the code of the contract at the address given by the last 20 bytes of its id.
    function storeInCode(Market memory market) internal returns (address create2Address) {
        // forge-lint: disable-next-item(encode-packed-collision) there is no ambiguity since SSTORE2_PREFIX has a fixed size.
        bytes memory creationCode = abi.encodePacked(SSTORE2_PREFIX, abi.encode(market));
        assembly ("memory-safe") {
            create2Address := create2(0, add(creationCode, 0x20), mload(creationCode), 0)
        }
        require(create2Address != address(0), SStore2DeploymentFailed());
    }
}
