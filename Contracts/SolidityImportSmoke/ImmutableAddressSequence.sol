// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Address immutables without an inline initializer. `GUARD` and `PAYEE` come from constructor
/// arguments, so the source does not determine them; `SELF` is assigned `address(this)` once, at
/// the top level of the constructor. A custom error carries an immutable as an argument.
contract SequenceFixture {
    address private immutable GUARD;
    address public immutable PAYEE;
    address private immutable SELF;

    uint256 private value;
    mapping(address => uint256) private credit;

    error NotGuard(address caller);
    error NotPayee(address caller, address payee);

    event Credited(address indexed to, uint256 amount);

    constructor(address guard_, address payee_) {
        require(guard_ != address(0) && payee_ != address(0), NotGuard(address(0)));
        GUARD = guard_;
        PAYEE = payee_;
        SELF = address(this);
    }

    function change(uint256 x) external returns (uint256) {
        require(msg.sender == GUARD, NotGuard(msg.sender));
        value = x;
        credit[PAYEE] += x;
        emit Credited(PAYEE, x);
        return value;
    }

    function isGuard() external view returns (bool) {
        return msg.sender == GUARD;
    }

    function payeeCredit() external view returns (uint256) {
        return credit[PAYEE];
    }

    function notDelegated() external view returns (bool) {
        return address(this) == SELF;
    }

    function fail() external view {
        require(value <= 15, "range");
        require(msg.sender == PAYEE, NotPayee(msg.sender, PAYEE));
    }

    function read() external view returns (uint256) {
        return value;
    }
}
