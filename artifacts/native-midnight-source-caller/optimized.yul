/// @use-src 0:"SourceCaller.sol"
object "SourceCaller_34" {
    code {
        {
            /// @src 0:169:417  "contract SourceCaller {..."
            let _1 := memoryguard(0x80)
            mstore(64, _1)
            if callvalue() { revert(0, 0) }
            let _2 := datasize("SourceCaller_34_deployed")
            codecopy(_1, dataoffset("SourceCaller_34_deployed"), _2)
            return(_1, _2)
        }
    }
    /// @use-src 0:"SourceCaller.sol", 2:"src/libraries/IdLib.sol"
    object "SourceCaller_34_deployed" {
        code {
            {
                /// @src 0:169:417  "contract SourceCaller {..."
                let _1 := memoryguard(0x80)
                mstore(64, _1)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x30ccca8f {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 96) { revert(0, 0) }
                        let offset := calldataload(4)
                        if gt(offset, 0xffffffffffffffff) { revert(0, 0) }
                        if slt(add(sub(calldatasize(), offset), not(3)), 0x0100) { revert(0, 0) }
                        let newFreePtr := add(_1, 0x0100)
                        if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, _1))
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x41)
                            revert(0, 0x24)
                        }
                        mstore(64, newFreePtr)
                        mstore(_1, calldataload(add(4, offset)))
                        let _2 := abi_decode_address(add(offset, 36))
                        let _3 := add(_1, 32)
                        mstore(_3, _2)
                        let _4 := abi_decode_address(add(offset, 68))
                        let _5 := add(_1, 64)
                        mstore(_5, _4)
                        let offset_1 := calldataload(add(offset, 100))
                        if gt(offset_1, 0xffffffffffffffff) { revert(0, 0) }
                        let _6 := add(offset, offset_1)
                        if iszero(slt(add(_6, 35), calldatasize())) { revert(0, 0) }
                        let length := calldataload(add(_6, 4))
                        if gt(length, 0xffffffffffffffff)
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x41)
                            revert(0, 36)
                        }
                        let memPtr := mload(64)
                        finalize_allocation(memPtr, add(shl(5, length), 32))
                        let dst := memPtr
                        mstore(memPtr, length)
                        dst := add(memPtr, 32)
                        let srcEnd := add(add(add(_6, shl(7, length)), 4), 32)
                        if gt(srcEnd, calldatasize()) { revert(0, 0) }
                        let src := add(_6, 36)
                        for { } lt(src, srcEnd) { src := add(src, 0x80) }
                        {
                            if slt(sub(calldatasize(), src), 0x80) { revert(0, 0) }
                            let memPtr_1 := mload(64)
                            let newFreePtr_1 := add(memPtr_1, 0x80)
                            if or(gt(newFreePtr_1, 0xffffffffffffffff), lt(newFreePtr_1, memPtr_1))
                            {
                                mstore(0, shl(224, 0x4e487b71))
                                mstore(4, 0x41)
                                revert(0, 36)
                            }
                            mstore(64, newFreePtr_1)
                            mstore(memPtr_1, abi_decode_address(src))
                            mstore(add(memPtr_1, 32), calldataload(add(src, 32)))
                            mstore(add(memPtr_1, 64), calldataload(add(src, 64)))
                            mstore(add(memPtr_1, 96), abi_decode_address(add(src, 96)))
                            mstore(dst, memPtr_1)
                            dst := add(dst, 32)
                        }
                        let _7 := add(_1, 96)
                        mstore(_7, memPtr)
                        let _8 := add(_1, 0x80)
                        mstore(_8, calldataload(add(offset, 132)))
                        let _9 := add(_1, 160)
                        mstore(_9, calldataload(add(offset, 164)))
                        let _10 := abi_decode_address(add(offset, 196))
                        let _11 := add(_1, 192)
                        mstore(_11, _10)
                        let _12 := abi_decode_address(add(offset, 228))
                        let _13 := add(_1, 224)
                        mstore(_13, _12)
                        mstore(0, calldataload(36))
                        mstore(32, 0)
                        sstore(keccak256(0, 64), calldataload(68))
                        let memPtr_2 := mload(64)
                        let newFreePtr_2 := add(memPtr_2, 64)
                        if or(gt(newFreePtr_2, 0xffffffffffffffff), lt(newFreePtr_2, memPtr_2))
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x41)
                            revert(0, 36)
                        }
                        mstore(64, newFreePtr_2)
                        mstore(memPtr_2, 11)
                        let _14 := add(memPtr_2, 32)
                        mstore(_14, shl(168, 0x600b380380600b5f395ff3))
                        /// @src 2:2055:2073  "abi.encode(market)"
                        let expr_mpos := /** @src 0:169:417  "contract SourceCaller {..." */ mload(64)
                        /// @src 2:2055:2073  "abi.encode(market)"
                        let _15 := add(expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 32)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        mstore(_15, /** @src 0:169:417  "contract SourceCaller {..." */ 32)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        let tail := add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ 320)
                        /// @src 0:169:417  "contract SourceCaller {..."
                        mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 64), /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_1))
                        /// @src 0:169:417  "contract SourceCaller {..."
                        mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 96), and(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_3), /** @src 0:169:417  "contract SourceCaller {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 0x80), and(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_5), /** @src 0:169:417  "contract SourceCaller {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        let memberValue0 := mload(_7)
                        mstore(add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 160), 0x0100)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        let pos := tail
                        let length_1 := mload(memberValue0)
                        mstore(tail, length_1)
                        pos := add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ 352)
                        let srcPtr := add(memberValue0, /** @src 0:169:417  "contract SourceCaller {..." */ 32)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        let i := /** @src 0:169:417  "contract SourceCaller {..." */ 0
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        for { }
                        lt(i, length_1)
                        {
                            i := add(i, /** @src 0:169:417  "contract SourceCaller {..." */ 1)
                        }
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        {
                            let _16 := mload(srcPtr)
                            /// @src 0:169:417  "contract SourceCaller {..."
                            mstore(pos, and(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_16), /** @src 0:169:417  "contract SourceCaller {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(pos, /** @src 0:169:417  "contract SourceCaller {..." */ 32), /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(add(_16, /** @src 0:169:417  "contract SourceCaller {..." */ 32)))
                            mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(pos, /** @src 0:169:417  "contract SourceCaller {..." */ 64), /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(add(_16, /** @src 0:169:417  "contract SourceCaller {..." */ 64)))
                            mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(pos, /** @src 0:169:417  "contract SourceCaller {..." */ 96), and(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(add(_16, /** @src 0:169:417  "contract SourceCaller {..." */ 96)), 0xffffffffffffffffffffffffffffffffffffffff))
                            /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                            pos := add(pos, /** @src 0:169:417  "contract SourceCaller {..." */ 0x80)
                            /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                            srcPtr := add(srcPtr, /** @src 0:169:417  "contract SourceCaller {..." */ 32)
                        }
                        mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 192), /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_8))
                        /// @src 0:169:417  "contract SourceCaller {..."
                        mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 224), /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_9))
                        /// @src 0:169:417  "contract SourceCaller {..."
                        mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 0:169:417  "contract SourceCaller {..." */ 0x0100), and(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_11), /** @src 0:169:417  "contract SourceCaller {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ add(/** @src 2:2055:2073  "abi.encode(market)" */ expr_mpos, /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ 288), /** @src 0:169:417  "contract SourceCaller {..." */ and(/** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ mload(_13), /** @src 0:169:417  "contract SourceCaller {..." */ 0xffffffffffffffffffffffffffffffffffffffff))
                        /// @src 2:2055:2073  "abi.encode(market)"
                        let _17 := sub(pos, expr_mpos)
                        mstore(expr_mpos, add(_17, /** @src 0:169:417  "contract SourceCaller {..." */ not(31)))
                        /// @src 2:2055:2073  "abi.encode(market)"
                        finalize_allocation(expr_mpos, _17)
                        /// @src 2:2022:2074  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                        let expr_mpos_1 := /** @src 0:169:417  "contract SourceCaller {..." */ mload(64)
                        /// @src 2:2022:2074  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                        let _18 := add(expr_mpos_1, /** @src 0:169:417  "contract SourceCaller {..." */ 32)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        let length_2 := mload(memPtr_2)
                        mcopy(_18, _14, length_2)
                        let _19 := add(/** @src 2:2022:2074  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))" */ expr_mpos_1, /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ length_2)
                        let _20 := add(_19, /** @src 0:169:417  "contract SourceCaller {..." */ 32)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        mstore(_20, /** @src 0:169:417  "contract SourceCaller {..." */ 0)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        let length_3 := mload(expr_mpos)
                        mcopy(_20, _15, length_3)
                        let _21 := add(add(_19, length_3), /** @src 0:169:417  "contract SourceCaller {..." */ 32)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        mstore(_21, /** @src 0:169:417  "contract SourceCaller {..." */ 0)
                        /// @src 2:2022:2074  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                        let _22 := sub(_21, expr_mpos_1)
                        mstore(expr_mpos_1, add(_22, /** @src 0:169:417  "contract SourceCaller {..." */ not(31)))
                        /// @src 2:2022:2074  "abi.encodePacked(SSTORE2_PREFIX, abi.encode(market))"
                        finalize_allocation(expr_mpos_1, _22)
                        /// @src 0:169:417  "contract SourceCaller {..."
                        let _23 := and(/** @src 2:2084:2210  "assembly (\"memory-safe\") {..." */ create2(/** @src 0:169:417  "contract SourceCaller {..." */ 0, /** @src 2:2084:2210  "assembly (\"memory-safe\") {..." */ _18, mload(expr_mpos_1), /** @src 0:169:417  "contract SourceCaller {..." */ 0), 0xffffffffffffffffffffffffffffffffffffffff)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        if /** @src 2:2227:2255  "create2Address != address(0)" */ iszero(/** @src 0:169:417  "contract SourceCaller {..." */ _23)
                        /// @src 2:1167:1194  "hex\"600b380380600b5f395ff3\""
                        {
                            mstore(/** @src 0:169:417  "contract SourceCaller {..." */ 0, /** @src 2:1167:1194  "hex\"600b380380600b5f395ff3\"" */ shl(225, 0x41b2ccbf))
                            revert(/** @src 0:169:417  "contract SourceCaller {..." */ 0, 4)
                        }
                        let memPos := mload(64)
                        mstore(memPos, _23)
                        return(memPos, 32)
                    }
                    case 0x5e383d21 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 32) { revert(0, 0) }
                        mstore(0, calldataload(4))
                        mstore(32, 0)
                        let _24 := sload(keccak256(0, 64))
                        let memPos_1 := mload(64)
                        mstore(memPos_1, _24)
                        return(memPos_1, 32)
                    }
                }
                revert(0, 0)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 0:169:417  "contract SourceCaller {..." */ shl(224, 0x4e487b71))
                    mstore(4, 0x41)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 0:169:417  "contract SourceCaller {..." */ 0x24)
                }
                mstore(64, newFreePtr)
            }
            function abi_decode_address(offset) -> value
            {
                value := calldataload(offset)
                if iszero(eq(value, and(value, 0xffffffffffffffffffffffffffffffffffffffff))) { revert(0, 0) }
            }
        }
        data ".metadata" hex"a164736f6c6343000822000a"
    }
}
