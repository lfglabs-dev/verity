pragma solidity 0.8.34;

uint256 constant SCALE = 1e18;
uint256 constant FEE = 0.000014e18;
uint256 constant CAP = 1_000_000;
uint32 constant RATE = uint32(uint256(0.01e18) / uint256(365 days));
uint256 constant LOCK_SLOT = uint256(keccak256("verity.import.lock"));
bytes32 constant TAG = keccak256("verity.import.tag");
uint8 constant SMALL = 4;
uint256 constant WINDOW = 2 hours + 30 minutes;
uint256 constant DERIVED = SCALE / 1000 * 3;
uint256 constant MASK = 0xff_ff;
uint256 constant BIG = 2 ** 255 + (7 - 3) * 10 ** 3 / 8;
