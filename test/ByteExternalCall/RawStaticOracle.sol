// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IRawStaticOracle {
    function price() external view returns (uint256);
}

contract OracleSequenceCaller {
    uint256 private saved;

    function read(address target, uint256 next) external returns (uint256) {
        saved = next;
        return IRawStaticOracle(target).price();
    }

    function readAndReject(address target, uint256 next, uint256 reject)
        external returns (uint256)
    {
        saved = next;
        uint256 result = IRawStaticOracle(target).price();
        if (reject != 0) {
            assembly ("memory-safe") { revert(0, 0) }
        }
        return result;
    }
}

// Constructor-only configuration: every runtime selector uses the fallback.
contract RawStaticOracle {
    uint256 private value;
    bool private failed;
    uint256 private length;

    constructor(uint256 v, bool f, uint256 n) {
        value = v;
        failed = f;
        length = n;
    }

    fallback() external {
        uint256 v = value;
        bool f = failed;
        uint256 n = length;
        assembly ("memory-safe") {
            mstore(0, v)
            if f { revert(0, n) }
            return(0, n)
        }
    }
}
