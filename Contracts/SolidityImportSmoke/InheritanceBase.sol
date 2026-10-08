// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IInheritanceObserver {
    function read() external view returns (uint256);
}

abstract contract InheritanceRoot is IInheritanceObserver {
    uint256 internal rootTouch;
    event StepRecorded(uint256 indexed chained, uint256 indexed bonus);

    function _rootSecret(uint256 x) private pure returns (uint256) {
        return (x % 17) + 3;
    }

    function computeBonus(uint256 x) internal view virtual returns (uint256) {
        return rootTouch + x + 2;
    }

    function viaVirtual(uint256 x) internal view returns (uint256) {
        return computeBonus(x) + _rootSecret(x);
    }

    function step(uint256 x) internal virtual returns (uint256) {
        rootTouch = x + 1;
        return rootTouch;
    }

    function fail() external virtual {
        rootTouch = 99;
        emit StepRecorded(99, 99);
        require(false, "inheritance failure");
    }

    function read() external view virtual override returns (uint256) {
        return rootTouch + viaVirtual(rootTouch);
    }
}

abstract contract InheritanceLeft is InheritanceRoot {
    uint256 internal leftTouch;
    uint256[4] private __gap;

    function step(uint256 x) internal virtual override returns (uint256) {
        uint256 prev = super.step(x);
        leftTouch = prev + 10;
        return leftTouch;
    }
}

abstract contract InheritanceRight is InheritanceRoot {
    uint256 internal rightTouch;
    uint256[4] private __gap;

    function step(uint256 x) internal virtual override returns (uint256) {
        uint256 prev = super.step(x);
        rightTouch = prev + 100;
        return rightTouch;
    }
}
