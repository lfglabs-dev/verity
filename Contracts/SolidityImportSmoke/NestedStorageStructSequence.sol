// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Whole-struct assignment to nested storage sub-structs from memory/calldata (#2729) and
// returning/reading nested storage sub-structs as flat memory structs (#2730), across a
// top-level struct, 1-key and 2-key struct mappings, a two-level nested sub-struct, and an
// ERC-7201 raw-slot struct, with packed unsigned/signed/bool fields and preserved siblings.
contract SequenceFixture {
    struct Leaf {
        uint64 left;
        bool active;
    }

    struct Mid {
        Leaf leaf;
        uint128 count;
    }

    struct Part {
        uint128 low;
        bool enabled;
        int24 delta;
        uint64 high;
        uint256 full;
    }

    struct Record {
        uint64 head;
        Part part;
        Mid mid;
        uint128 tail;
        uint256[] items;
    }

    struct RawBox {
        uint128 beforePart;
        Part part;
        uint128 afterPart;
    }

    bytes32 private constant RAW_SLOT =
        0x7147d037fd90a15f43a59801d27c0e7741a4e051613665d1fc3df28638d8c500;

    Record private topRecord;
    mapping(address => Record) private records;
    mapping(bytes32 => mapping(address => Record)) private pairRecords;

    function _rawBox() private pure returns (RawBox storage $) {
        assembly ("memory-safe") {
            $.slot := RAW_SLOT
        }
    }

    function _makePart(uint256 x) private pure returns (Part memory) {
        int24 d = int24(int256((x >> 8) & 0xffff) - 32768);
        return Part({
            low: uint128(x) + 1,
            enabled: (x & 1) == 0,
            delta: d,
            high: uint64(x >> 24) + 3,
            full: x ^ 0x55aa55aa
        });
    }

    function _loadPart(address k) private view returns (Part memory) {
        return records[k].part;
    }

    function _scorePart(Part memory p) private pure returns (uint256) {
        uint256 signedTerm = uint256(int256(p.delta) + 0x1000000);
        return (uint256(p.low) % 1000003) * 3 + (p.enabled ? 11 : 5) + signedTerm * 7 +
            (uint256(p.high) % 1000003) * 13 + (p.full % 1000003) * 17;
    }

    function change(uint256 x) external returns (uint256) {
        bytes32 bucket = bytes32(x % 3);
        topRecord.head = uint64((x % 97) + 1);
        topRecord.tail = uint128((x % 89) + 2);
        if (topRecord.items.length < 3) {
            topRecord.items.push(x % 251);
        }
        records[msg.sender].head = uint64((x % 83) + 4);
        records[msg.sender].tail = uint128((x % 79) + 6);
        records[msg.sender].mid.count = uint128((x % 73) + 8);
        if (records[msg.sender].items.length < 2) {
            records[msg.sender].items.push((x % 241) + 1);
        }
        pairRecords[bucket][msg.sender].head = uint64((x % 71) + 5);
        pairRecords[bucket][msg.sender].tail = uint128((x % 67) + 7);
        RawBox storage box = _rawBox();
        box.beforePart = uint128((x % 61) + 9);
        box.afterPart = uint128((x % 59) + 10);

        Part memory built = _makePart(x);
        Part memory alt = Part(
            uint128((x % 1000) + 9),
            (x & 2) != 0,
            -int24(int256((x % 500) + 1)),
            uint64((x % 700) + 11),
            (x % 9000) + 13
        );
        topRecord.part = (x & 4) == 0 ? built : alt;
        records[msg.sender].part = built;
        pairRecords[bucket][msg.sender].part = alt;
        box.part = built;

        Leaf memory lf = Leaf(uint64((x % 409) + 15), (x & 8) != 0);
        topRecord.mid.leaf = lf;
        records[msg.sender].mid.leaf = Leaf({left: uint64((x % 307) + 19), active: (x & 16) == 0});

        Part memory fromOne = _loadPart(msg.sender);
        Part memory fromZero = topRecord.part;
        Part memory fromTwo = pairRecords[bucket][msg.sender].part;
        Part memory fromRaw = box.part;
        Leaf memory leafZero = topRecord.mid.leaf;
        Leaf memory leafOne = records[msg.sender].mid.leaf;

        uint256 siblings = uint256(topRecord.head) + uint256(topRecord.tail) +
            topRecord.items[0] + uint256(records[msg.sender].head) +
            uint256(records[msg.sender].tail) + uint256(records[msg.sender].mid.count) +
            records[msg.sender].items[0] + uint256(pairRecords[bucket][msg.sender].head) +
            uint256(pairRecords[bucket][msg.sender].tail) + uint256(box.beforePart) +
            uint256(box.afterPart);
        uint256 leaves = uint256(leafZero.left) + (leafZero.active ? 23 : 0) +
            uint256(leafOne.left) + (leafOne.active ? 29 : 0);
        return _scorePart(fromOne) + _scorePart(fromZero) * 2 + _scorePart(fromTwo) * 3 +
            _scorePart(fromRaw) * 5 + siblings + leaves;
    }

    function writePartMemory(address k, Part memory p) external {
        require(k != address(0), "zero key");
        records[k].part = p;
    }

    function writePartCalldata(address k, Part calldata p) external {
        require(k != address(0), "zero key");
        records[k].part = p;
    }

    function readPart(address k) external view returns (Part memory) {
        return records[k].part;
    }

    function readNamedPart(address k) external view returns (Part memory out) {
        if (k == address(0)) {
            return out;
        }
        out = records[k].part;
    }

    function fail() external view {
        require(topRecord.head == 999999, "blocked");
    }

    function read() external view returns (uint256) {
        Part memory p = records[msg.sender].part;
        Leaf memory lf = records[msg.sender].mid.leaf;
        return _scorePart(p) + uint256(lf.left) + (lf.active ? 31 : 0) +
            uint256(topRecord.head) + uint256(topRecord.tail) + topRecord.items.length;
    }
}
