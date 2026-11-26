// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

interface IEncodingScalarTarget {
    function accept(uint256 a, uint256 b) external;
    function acceptBytes(bytes calldata data, uint256 a, uint256 b) external;
}

// Checked binary operations and conditionals in unordered `checkEncodingScalar` positions
// (`abi.encode` static without hoistable siblings and dynamic with `bytes`, `abi.encodePacked`,
// `bytes.concat`, `abi.encodeWithSelector` selector and payload, `abi.encodeWithSignature`,
// `abi.encodeCall` static and `bytes`, static struct constructor arguments, and dynamic `emit`
// data) in a contract with a single state variable (#2830).
// `change(x)` selects a branch with `c = x % 8`, `flag = ((x / 8) % 2 == 1)` and `y = x / 16`:
// `y = 0` triggers competing panics (`10 / y` vs `y - 1`, right-first on legacy and left-first on
// via-IR inside binary operands, left-to-right across arguments, and short-circuiting on
// `&&` / `||` and `?:`), while large `x` overflows `y * 32` (`Panic(0x11)`).
contract SequenceFixture {
    struct Pair {
        uint8 a;
        uint256 b;
    }

    uint256 stored;

    event PayloadObserved(string tag, uint256 first, uint256 second);
    event Written(uint256 branch, uint256 value);

    function change(uint256 x) external {
        uint256 c = x % 8;
        bool flag = ((x / 8) % 2 == 1);
        uint256 y = x / 16;
        uint256 r;
        if (c == 0) {
            bytes32 h1 = keccak256(abi.encode((10 / y) + (y - 1), y + 3));
            bytes32 h2 = keccak256(abi.encode(flag && (10 / y > 0), (flag == false) || (y - 1 > 0)));
            r = uint256(h1 ^ h2) % 1000000 + stored;
        } else if (c == 1) {
            bytes32 h = keccak256(abi.encode(flag ? 10 / y : 7, flag ? stored + 5 : y - 1));
            r = uint256(h) % 1000000;
        } else if (c == 2) {
            bytes32 h = keccak256(abi.encode("tag", y + 10, flag ? stored + 1 : 10 / y));
            emit PayloadObserved("obs", flag ? 10 / y : y + 1, stored);
            r = uint256(h) % 1000000;
        } else if (c == 3) {
            uint8 u = uint8(y % 251);
            int8 s = int8(uint8(y % 120));
            bytes32 h1 = keccak256(abi.encodePacked(
                uint16(y + 1),
                s + int8(3),
                flag ? uint8(10 / y) : u + uint8(4)
            ));
            bytes32 h2;
            unchecked {
                h2 = keccak256(bytes.concat(
                    bytes32(y - 1),
                    flag ? bytes4(0x11223344) : bytes4(uint32(u + uint8(200)))
                ));
            }
            r = uint256(h1 ^ h2) % 1000000;
        } else if (c == 4) {
            bytes32 h1 = keccak256(abi.encodeWithSelector(
                flag ? bytes4(0x12345678) : bytes4(uint32(10 / y)),
                y + 1,
                flag ? stored : y - 1
            ));
            bytes32 h2 = keccak256(abi.encodeWithSelector(
                IEncodingScalarTarget.acceptBytes.selector,
                "dyn",
                flag ? y + 2 : 10 / y,
                stored + 1
            ));
            r = uint256(h1 ^ h2) % 1000000;
        } else if (c == 5) {
            bytes32 h1 = keccak256(abi.encodeWithSignature(
                "accept(uint256,uint256)",
                y + 1,
                flag ? stored : 10 / y
            ));
            bytes32 h2 = keccak256(abi.encodeWithSignature(
                "acceptBytes(bytes,uint256,uint256)",
                "sig",
                flag ? 10 / y : y + 1,
                stored + 2
            ));
            r = uint256(h1 ^ h2) % 1000000;
        } else if (c == 6) {
            bytes32 h1 = keccak256(abi.encodeCall(
                IEncodingScalarTarget.accept,
                (y + 1, flag ? stored : y - 1)
            ));
            bytes32 h2 = keccak256(abi.encodeCall(
                IEncodingScalarTarget.acceptBytes,
                ("call", flag ? 10 / y : y + 1, stored + 3)
            ));
            r = uint256(h1 ^ h2) % 1000000;
        } else {
            bytes32 h = keccak256(abi.encode(
                Pair(uint8(y % 200) + uint8(1), flag ? stored + 4 : y - 1),
                y * 32 + stored
            ));
            r = uint256(h) % 1000000;
        }
        stored = r;
        emit Written(c, r);
    }

    function fail() external {
        stored = 99;
        require(stored < 1, "rollback unordered encoding write");
    }

    function read() external view returns (uint256) {
        return stored;
    }
}
