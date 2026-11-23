// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Contract creation `new C(...)` must be handled the same way whatever else the contract
// declares (#2830). solc 0.8.34 runs CREATE on both pipelines: a fresh account at the address
// derived from this contract's nonce, the child's constructor with its own effects, and a
// constructor revert bubbled up. The importer does not model CREATE, so every form rejects at
// the call. The importer counts state variables across the whole compiled source, so the child
// contracts declare none and each contract of the pair is alone in its file; the pair differs
// only by one unrelated state variable and one unused function.
contract CreatedChild {
    event Built(uint256 a);

    constructor(uint256 a) payable {
        if (a == 0) revert("zero");
        emit Built(a);
    }
}

contract CreatedNamed {
    constructor(string memory name) {
        require(bytes(name).length != 0);
    }
}

contract ContractCreationOneSlot {
    uint256 internal stored;

    function build(uint256 a) internal returns (address) {
        return address(new CreatedChild(a));
    }

    function created(uint256 a) external returns (uint256) {
        CreatedChild c = new CreatedChild(a);
        stored = a;
        return uint256(uint160(address(c)));
    }

    function createdCode(uint256 a) external returns (uint256) {
        return address(new CreatedChild(a)).code.length;
    }

    function createdNamed(uint256 a) external returns (uint256) {
        stored = a;
        return uint256(uint160(address(new CreatedNamed("child"))));
    }

    function createdInHelper(uint256 a) external returns (uint256) {
        stored = a;
        return uint256(uint160(build(a)));
    }

    function createdStatement(uint256 a) external returns (uint256) {
        new CreatedChild(a);
        stored = a;
        return stored;
    }
}
