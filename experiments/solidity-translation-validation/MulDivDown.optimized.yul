/// @use-src 0:"MulDivDown.sol"
object "MulDivDown_23" {
    code {
        {
            /// @src 0:122:287  "contract MulDivDown {..."
            let _1 := memoryguard(0x80)
            mstore(64, _1)
            if callvalue() { revert(0, 0) }
            let _2 := datasize("MulDivDown_23_deployed")
            codecopy(_1, dataoffset("MulDivDown_23_deployed"), _2)
            return(_1, _2)
        }
    }
    /// @use-src 0:"MulDivDown.sol", 1:"src/libraries/UtilsLib.sol"
    object "MulDivDown_23_deployed" {
        code {
            {
                /// @src 0:122:287  "contract MulDivDown {..."
                let _1 := memoryguard(0x80)
                mstore(64, _1)
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0xb67bee04, shr(224, calldataload(0)))
                    {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 96) { revert(0, 0) }
                        let value := calldataload(4)
                        let value_1 := calldataload(36)
                        let value_2 := calldataload(68)
                        let product := mul(value, value_1)
                        if iszero(or(iszero(value), eq(value_1, div(product, value))))
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x11)
                            revert(0, 36)
                        }
                        if iszero(value_2)
                        {
                            mstore(0, shl(224, 0x4e487b71))
                            mstore(4, 0x12)
                            revert(0, 36)
                        }
                        mstore(_1, div(product, value_2))
                        return(_1, 32)
                    }
                }
                revert(0, 0)
            }
        }
        data ".metadata" hex"a164736f6c6343000822000a"
    }
}
