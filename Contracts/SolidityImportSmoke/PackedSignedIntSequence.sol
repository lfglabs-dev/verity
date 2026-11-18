// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// `abi.encodePacked` of narrow signed integers packs each value into its own width (the low
// bytes of its sign-extended word), mixed with address, bytes32 and unsigned operands,
// for negative and positive values, both hashed and as a buffer length.
contract SequenceFixture {
    bytes32 private last;
    uint256 private total;
    function change(uint256 x) external returns (bytes32) {
        int8 s = int8(int256(x & 0xff) - 128);
        int24 t = int24(int256((x >> 8) & 0xffffff) - 8388608);
        int128 w = int128(int256((x >> 32) & 0xffffffffffffffffffffffffffffffff) -
            0x80000000000000000000000000000000);
        address who = address(uint160(x >> 96));
        uint16 small = uint16(x >> 240);
        bytes32 h = keccak256(abi.encodePacked(who, t, s, bytes32(x), w, small));
        bytes memory buffer = abi.encodePacked(t, s, w);
        total = total + buffer.length;
        last = h ^ keccak256(buffer);
        return last;
    }
    function fail() external {
        bytes memory one = abi.encodePacked(int8(-1));
        // solc packs one byte, so this reverts; a 32-byte packing would not.
        require(one.length == 32);
    }
    function read() external view returns (bytes32) {
        return last;
    }
}
