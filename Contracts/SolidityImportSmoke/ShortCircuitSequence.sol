pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 divisor;
    mapping(address => bool) accepted;

    function guarded(uint256 value) internal pure returns (bool) {
        require(value != 7, "guarded RHS evaluated");
        return value > 1;
    }

    function change(uint256 value) external returns (bool, bool, bool, bool) {
        divisor = value;
        accepted[msg.sender] = true;
        bool either = value == 0 || 100 / value > 1;
        bool both = value != 0 && 100 / value > 1;
        bool helper = value == 7 || guarded(value);
        bool nested = (value == 0 || accepted[msg.sender]) && (value == 7 || guarded(value));
        return (either, both, helper, nested);
    }

    function fail() external returns (bool) {
        divisor = 0;
        return false || 100 / divisor > 1;
    }

    function read() external view returns (bool, bool) {
        return (true || 100 / divisor > 1, false && accepted[msg.sender]);
    }
}
