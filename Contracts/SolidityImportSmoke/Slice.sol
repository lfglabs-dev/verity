// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

import "./Lib.sol";

struct Pos {
    uint128 credit;
    uint128 pendingFee;
    uint128 lastLossFactor;
    uint128 lastAccrual;
    uint128 debt;
    uint128 collateralBitmap;
}

struct MktState {
    uint128 totalUnits;
    uint128 lossFactor;
}

struct Mkt {
    uint256 ignored;
    uint128[] collateralParams;
    uint256 maturity;
}

contract C {
    using L for uint256;
    using L for uint128;

    mapping(bytes32 => mapping(address => Pos)) public position;
    mapping(bytes32 => MktState) public marketState;

    function f(Mkt memory m, bytes32 id, address user)
        external
        view
        returns (uint128, uint128, uint128)
    {
        Pos storage p = position[id][user];
        uint128 credit = p.credit;
        uint128 lastLoss = p.lastLossFactor;
        uint256 post = lastLoss < type(uint128).max
            ? credit.mulDivDown(type(uint128).max - marketState[id].lossFactor, type(uint128).max - lastLoss)
            : 0;
        uint128 pending = p.pendingFee;
        uint256 postFee = credit > 0 ? pending - pending.mulDivUp(credit - post, credit) : 0;
        uint256 end = L.min(block.timestamp, m.maturity);
        uint128 lastAccrual = p.lastAccrual;
        uint128 fee = lastAccrual < m.maturity
            ? uint128(postFee.mulDivDown(end - lastAccrual, m.maturity - lastAccrual))
            : 0;
        return (uint128(post) - fee, uint128(postFee) - fee, fee);
    }

    function lossOf(bytes32 market) external view returns (uint128) {
        return marketState[market].lossFactor;
    }
}
