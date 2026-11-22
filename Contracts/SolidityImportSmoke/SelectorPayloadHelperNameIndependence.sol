// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// A private helper taking an address and an `abi.encodeWithSelector(I.f.selector, ...)` payload is
// modeled by its own body, whatever it is called. The helper name `_callOptionalReturn` once
// selected a fixed optional-bool CALL lowering in place of the body.

interface ITarget {
    function ping(address to, uint256 amount) external returns (bool);
}

// The same body under two names: both must import, and agree with solc.
contract SelectorPayloadHelperNameIndependence {
    uint256 private first = 7;
    uint256 private second = 9;

    function _callOptionalReturn(address token, bytes memory data) private pure {
        require(token != address(0));
        require(data.length == 68);
    }

    function checkPayload(address token, bytes memory data) private pure {
        require(token != address(0));
        require(data.length == 68);
    }

    function viaOptionalName(address token, uint256 amount) external pure returns (uint256) {
        _callOptionalReturn(token, abi.encodeWithSelector(ITarget.ping.selector, token, amount));
        return amount + 1;
    }

    function viaOtherName(address token, uint256 amount) external pure returns (uint256) {
        checkPayload(token, abi.encodeWithSelector(ITarget.ping.selector, token, amount));
        return amount + 1;
    }
}
