// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IPeer {
    function ping(uint256 x) external view returns (uint256);
}

contract SequenceFixture {
    IPeer private activePeer;
    mapping(uint256 => IPeer) private peerBySlot;
    int256 private signedAccumulator;
    mapping(uint256 => int256) private signedDeltaBySlot;

    function _selectPeer(IPeer candidate, IPeer fallbackPeer, bool preferCandidate) internal pure returns (IPeer) {
        return preferCandidate ? candidate : fallbackPeer;
    }

    function _adjustSigned(int256 baseDelta, int256 step) internal pure returns (int256) {
        baseDelta += step;
        baseDelta -= 3;
        int256 flipped = -step;
        int256 scaled = (baseDelta * 5) / (-2) + (flipped * 3) / 2;
        if (scaled < -10 && baseDelta >= -5) {
            scaled += 4;
        } else if (scaled > 10 || baseDelta <= -6) {
            scaled -= 2;
        }
        int256 boundTag = (type(int256).max > 0 && type(int256).min < 0 && type(uint256).min == 0)
            ? int256(7)
            : int256(-7);
        int256 wrapProbe;
        unchecked {
            int256 maxEdge = type(int256).max + 1;
            int256 minEdge = type(int256).min - 1;
            int256 negMin = -type(int256).min;
            wrapProbe = (maxEdge - negMin) + (minEdge - type(int256).max);
        }
        return scaled + boundTag + wrapProbe;
    }

    function change(uint256 input) external returns (uint256) {
        if (input == 96) {
            int256 one = int256(input - 95);
            signedAccumulator = type(int256).max + one;
        }
        if (input == 97) {
            int256 one = int256(input - 96);
            signedAccumulator = type(int256).min - one;
        }
        if (input == 98) {
            int256 negOne = -int256(input - 97);
            signedAccumulator = type(int256).min / negOne;
        }
        uint256 seed = input % 100000;
        uint256 slot = seed % 4;
        IPeer defaultPeer;
        IPeer candidate = IPeer(address(uint160(seed + 101)));
        IPeer chosen = _selectPeer(candidate, defaultPeer, (seed % 2) == 0);
        activePeer = chosen;
        peerBySlot[slot] = IPeer(msg.sender);
        int256 rawSigned = -int256((seed % 40) + 1);
        int256 adjusted = _adjustSigned(rawSigned, int256((seed % 11) + 2));
        signedDeltaBySlot[slot] += adjusted;
        signedAccumulator += signedDeltaBySlot[slot] - int256(slot);
        uint256 peerWord = uint256(uint160(address(activePeer))) + (peerBySlot[slot] == activePeer ? 1 : 2);
        require(input != 20, "int256 contract sequence rollback");
        return uint256(signedAccumulator) + uint256(signedDeltaBySlot[slot]) + peerWord;
    }

    function fail() external {
        signedAccumulator -= 777;
        require(false, "forced revert");
    }

    function read() external view returns (uint256) {
        return uint256(signedAccumulator)
            + uint256(signedDeltaBySlot[0]) + uint256(signedDeltaBySlot[1])
            + uint256(signedDeltaBySlot[2]) + uint256(signedDeltaBySlot[3])
            + uint256(uint160(address(activePeer)))
            + uint256(uint160(address(peerBySlot[0]))) + uint256(uint160(address(peerBySlot[1])))
            + uint256(uint160(address(peerBySlot[2]))) + uint256(uint160(address(peerBySlot[3])));
    }
}
