// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    error TransientLockActive(uint256 slot, uint256 previousValue);
    event MulmodTstoreObserved(uint256 indexed totalScore, bytes32 digest, uint256 lockState);

    uint256 private constant LOCK_SLOT_A = 0x1111;
    uint256 private constant LOCK_SLOT_B = 0x2222;

    uint256 private totalScore;
    uint128 private packedScale;
    uint64 private narrowCounter;
    int256 private signedMetric;
    bytes32 private lastDigest;
    mapping(uint256 => uint256) private bucketMul;

    function _tExchange(uint256 slot, uint256 nextValue) internal returns (uint256 prevValue) {
        assembly {
            let current := tload(slot)
            prevValue := current
            tstore(slot, nextValue)
        }
    }

    function _mulDivDown(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
        uint256 prod0;
        uint256 prod1;
        assembly {
            let mm := mulmod(x, y, not(0))
            prod0 := mul(x, y)
            prod1 := sub(sub(mm, prod0), lt(mm, prod0))
        }
        if (prod1 == 0) {
            return prod0 / denominator;
        }
        require(denominator > prod1, "mulDiv overflow");
        uint256 remainder;
        assembly {
            remainder := mulmod(x, y, denominator)
            prod1 := sub(prod1, gt(remainder, prod0))
            prod0 := sub(prod0, remainder)
        }
        unchecked {
            uint256 twos = denominator & (~denominator + 1);
            assembly {
                denominator := div(denominator, twos)
                prod0 := div(prod0, twos)
                twos := add(div(sub(0, twos), twos), 1)
            }
            prod0 |= prod1 * twos;
            uint256 inverse = (3 * denominator) ^ 2;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            result = prod0 * inverse;
            return result;
        }
    }

    function _yulMix(uint256 a, uint256 b, uint256 modVal) internal pure returns (uint256 out) {
        uint256 localAcc = a + 3;
        assembly {
            let step
            step := addmod(localAcc, b, modVal)
            let m := mulmod(step, add(b, 7), modVal)
            localAcc := xor(localAcc, m)
            a := add(a, step)
            out := add(localAcc, a)
        }
    }

    function change(uint256 input) external returns (uint256) {
        if (input == 21) {
            uint256 prev = _tExchange(LOCK_SLOT_A, 99);
            revert TransientLockActive(LOCK_SLOT_A, prev);
        }

        uint256 slotA = LOCK_SLOT_A;
        uint256 slotB = LOCK_SLOT_B;
        uint256 prevA = _tExchange(slotA, (input & 0xffff) + 1);
        uint256 afterA;
        assembly {
            let loaded := tload(slotA)
            tstore(slotB, add(loaded, 5))
            afterA := add(loaded, tload(slotB))
        }
        uint256 restoredA = _tExchange(slotA, prevA + 1);

        uint256 modBase = (input % 97) + 11;
        uint256 combined = afterA + restoredA + mulmod(input + 1000000, (1 << 200) + 7, modBase) + addmod(type(uint256).max - 5, input + 9, modBase);
        uint256 yulZeroMod;
        assembly {
            yulZeroMod := add(mulmod(input, 13, 0), addmod(input, 19, 0))
        }
        combined += yulZeroMod;

        uint256 scaled = _mulDivDown((1 << 192) + (input & 0xffffffff) + 3, (1 << 128) + ((input >> 3) & 0xffff) + 5, (1 << 160) + (modBase * 13));
        combined += (scaled & 0xffffffff) + _yulMix(input & 0xffff, scaled & 0xffff, modBase);

        uint256 factor = (input % 7) + 2;
        uint256 localProd = (input & 0xff) + 1;
        localProd *= factor;

        if (packedScale == 0) {
            packedScale = 3;
        } else {
            packedScale = uint128((uint256(packedScale) % 1000) + 1);
        }
        packedScale *= uint128(factor);

        unchecked {
            narrowCounter = uint64(input + 0x1000000000000001);
            narrowCounter *= uint64(factor + 0x100000001);
        }

        int256 sVal = int256(uint256(input & 0xff)) - 50;
        sVal *= -3;
        if (signedMetric == 0) {
            signedMetric = sVal;
        } else {
            unchecked {
                signedMetric *= sVal;
            }
        }

        uint256 bucketKey = input % 4;
        if (bucketMul[bucketKey] == 0) {
            bucketMul[bucketKey] = (input & 0x3f) + 2;
        } else {
            bucketMul[bucketKey] = (bucketMul[bucketKey] & 0xffff) + 1;
        }
        bucketMul[bucketKey] *= factor;

        uint256 pulseScore = _pulseLock(input & 3, (input >> 2) & 0xff, modBase);
        if (input == 19) {
            input *= 2;
            assembly {
                input := add(input, 3)
            }
        }
        combined += localProd + uint256(packedScale) + uint256(narrowCounter) + bucketMul[bucketKey] + pulseScore + (input & 0xff);
        bytes32 digest = keccak256(abi.encode(combined, signedMetric, prevA, restoredA));
        lastDigest = digest;
        totalScore += (uint256(digest) & 0xffffffff) + combined;
        emit MulmodTstoreObserved(totalScore, lastDigest, afterA);
        require(input != 20, "yul block mulmod tstore rollback");
        return totalScore;
    }

    function _pulseLock(uint256 slotKey, uint256 weight, uint256 denom) internal returns (uint256) {
        uint256 slot = LOCK_SLOT_A + (slotKey & 3);
        uint256 oldVal = _tExchange(slot, weight + 1);
        if (oldVal == 777) {
            revert TransientLockActive(slot, oldVal);
        }
        uint256 safeDenom = (denom % 251) + 1;
        uint256 mVal = mulmod(weight + 17, oldVal + 29, safeDenom);
        uint256 aVal = addmod(weight + 31, mVal + 43, safeDenom);
        weight &= 0xffff;
        weight += 2;
        weight *= ((denom % 5) + 2);
        assembly {
            let cur := tload(slot)
            let next := add(cur, add(mVal, aVal))
            tstore(slot, next)
            weight := add(weight, next)
        }
        uint256 finalLock = _tExchange(slot, 0);
        return weight + finalLock + oldVal;
    }

    function fail() external {
        _tExchange(LOCK_SLOT_A, 404);
        totalScore += 999;
        revert TransientLockActive(LOCK_SLOT_A, 404);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        uint256 slotA = LOCK_SLOT_A;
        uint256 slotB = LOCK_SLOT_B;
        uint256 currentLock;
        assembly {
            currentLock := add(tload(slotA), tload(slotB))
        }
        uint256 summary = uint256(packedScale) + uint256(narrowCounter) + uint256(signedMetric & 0xffff) + bucketMul[0] + bucketMul[1] + currentLock;
        return (totalScore, lastDigest, summary);
    }
}
