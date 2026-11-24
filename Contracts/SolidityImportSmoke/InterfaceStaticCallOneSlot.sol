// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IWordFeed {
    function quote(uint256 amount) external view returns (uint256);
    function byPeer(IWordFeed peer) external view returns (uint256);
    function narrow(uint128 amount, int256 delta, bytes4 tag) external view returns (uint256);
    function owner() external view returns (address);
    function small() external view returns (uint8);
    function rate() external view returns (uint16);
    function allowed(address account) external view returns (bool);
}

// A typed interface staticcall lowers the same way whatever else the contract declares
// (#2830): contract-typed parameters and receivers, narrow and signed parameters, `address`
// and `uint8`/`uint16` returns, converted arguments and expression positions other than whole
// statements. The importer counts state variables across the whole compiled source, so each
// contract of the pair is alone in its file; they differ only by one unrelated state variable
// and one unused function.
contract InterfaceStaticCallOneSlot {
    mapping(uint256 => uint256) internal stored;

    function peerQuote(address feed, address peer) external returns (uint256) {
        uint256 v = IWordFeed(feed).byPeer(IWordFeed(peer));
        stored[0] = v;
        return v;
    }

    function typedReceiver(IWordFeed feed, uint256 x) external returns (uint256) {
        uint256 v = feed.quote(x);
        stored[0] = v;
        return v;
    }

    function narrowQuote(address feed, uint128 amount, int256 delta, bytes4 tag)
        external
        returns (uint256)
    {
        uint256 v = IWordFeed(feed).narrow(amount, delta, tag);
        stored[0] = v;
        return v;
    }

    function ownerWord(address feed) external returns (uint256) {
        address a = IWordFeed(feed).owner();
        stored[0] = 1;
        return uint256(uint160(a));
    }

    function smallWord(address feed) external returns (uint256) {
        uint8 s = IWordFeed(feed).small();
        stored[0] = 1;
        return s;
    }

    function discardedOwner(address feed) external returns (uint256) {
        IWordFeed(feed).owner();
        stored[0] = 1;
        return 1;
    }

    function discardedSmall(address feed) external returns (uint256) {
        IWordFeed(feed).small();
        stored[0] = 1;
        return 1;
    }

    function rateWord(address feed) external returns (uint256) {
        uint16 r = IWordFeed(feed).rate();
        stored[0] = 1;
        return r;
    }

    function discardedRate(address feed) external returns (uint256) {
        IWordFeed(feed).rate();
        stored[0] = 1;
        return 1;
    }

    function convertedArgument(address feed, uint8 x) external returns (uint256) {
        uint256 v = IWordFeed(feed).quote(x);
        stored[0] = v;
        return v;
    }

    function returned(address feed, uint256 x) external returns (uint256) {
        stored[0] = x;
        return IWordFeed(feed).quote(x);
    }

    function leftOperand(address feed, uint256 x) external returns (uint256) {
        uint256 v = (x - 1) + IWordFeed(feed).quote(x);
        stored[0] = v;
        return v;
    }

    function rightOperand(address feed, uint256 x) external returns (uint256) {
        uint256 v = IWordFeed(feed).quote(x) + (x - 1);
        stored[0] = v;
        return v;
    }

    function compound(address feed, uint256 x) external returns (uint256) {
        uint256 v = x;
        v += IWordFeed(feed).quote(x);
        stored[0] = v;
        return v;
    }

    function mappingTarget(address feed, uint256 x) external returns (uint256) {
        stored[x] = IWordFeed(feed).quote(x);
        return stored[x];
    }

    function conditional(address feed, uint256 x) external returns (uint256) {
        uint256 v = x > 5 ? IWordFeed(feed).quote(x) : x - 1;
        stored[0] = v;
        return v;
    }

    function nestedReceiver(address feed, uint256 x) external returns (uint256) {
        uint256 v = IWordFeed(address(uint160(IWordFeed(feed).quote(x)))).quote(x);
        stored[0] = v;
        return v;
    }

    function helperReturn(address feed, uint256 x) external returns (uint256) {
        uint256 v = quoteOf(feed, x);
        stored[0] = v;
        return v;
    }

    function quoteOf(address feed, uint256 x) internal view returns (uint256) {
        return IWordFeed(feed).quote(x);
    }

    function helperArguments(address feed, uint256 x) external returns (uint256) {
        uint256 v = sum(x - 1, IWordFeed(feed).quote(x));
        stored[0] = v;
        return v;
    }

    function sum(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    function negatedCondition(address feed, address account) external returns (uint256) {
        stored[0] = 1;
        if (!IWordFeed(feed).allowed(account)) {
            return 0;
        }
        return 1;
    }

    function equalityRequire(address feed, uint256 x) external returns (uint256) {
        require(IWordFeed(feed).quote(x) == 5, "quote");
        stored[0] = x;
        return x;
    }
}
