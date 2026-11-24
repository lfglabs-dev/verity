// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

enum Version { V1, V2 }
type Amount is uint128;
interface IAsset {}

struct ConfigStruct { uint256 limit; Version version; }
struct PricedStruct { Amount amount; address owner; }
struct AssetStruct { IAsset asset; uint256 limit; }
struct PathStruct { uint256[] steps; Version[] versions; }

// Struct parameters whose fields are an enum, a user-defined value type, a contract type
// or an array of enums: each root is reported with the field's actual type.
contract StructFieldTypeSurvey {
    function configure(ConfigStruct calldata c) external pure returns (uint256) {
        return c.limit;
    }

    function price(PricedStruct calldata p) external pure returns (address) {
        return p.owner;
    }

    function hold(AssetStruct calldata a) external pure returns (uint256) {
        return a.limit;
    }

    function route(PathStruct calldata p) external pure returns (uint256) {
        return p.steps.length;
    }

    function plain(uint256 x) external pure returns (uint256) {
        return x;
    }
}
