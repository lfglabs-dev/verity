// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

contract ERC20Model {
    uint256 internal constant MAX_UINT256 = type(uint256).max;

    address private _owner;
    uint256 private _totalSupply;
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;

    constructor(address initialOwner) {
        _owner = initialOwner;
        _totalSupply = 0;
    }

    function mint(address to, uint256 amount) external {
        require(msg.sender == _owner, "Caller is not the owner");
        _balances[to] += amount;
        _totalSupply += amount;
    }

    function transfer(address to, uint256 amount) external {
        uint256 senderBal = _balances[msg.sender];
        require(senderBal >= amount, "Insufficient balance");

        if (msg.sender == to) {
            return;
        }

        _balances[msg.sender] = senderBal - amount;
        _balances[to] += amount;
    }

    function approve(address spender, uint256 amount) external {
        _allowances[msg.sender][spender] = amount;
    }

    function transferFrom(address fromAddr, address to, uint256 amount) external {
        uint256 currentAllowance = _allowances[fromAddr][msg.sender];
        require(currentAllowance >= amount, "Insufficient allowance");

        uint256 fromBalance = _balances[fromAddr];
        require(fromBalance >= amount, "Insufficient balance");

        if (fromAddr != to) {
            _balances[fromAddr] = fromBalance - amount;
            _balances[to] += amount;
        }

        if (currentAllowance != MAX_UINT256) {
            _allowances[fromAddr][msg.sender] = currentAllowance - amount;
        }
    }

    function balanceOf(address addr) external view returns (uint256) {
        return _balances[addr];
    }

    function allowanceOf(address ownerAddr, address spender) external view returns (uint256) {
        return _allowances[ownerAddr][spender];
    }

    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    function owner() external view returns (address) {
        return _owner;
    }
}

contract PropertyERC20Test is Test {
    ERC20Model internal token;

    address internal constant OWNER = address(0xA11CE);
    address internal constant ALICE = address(0xA1);
    address internal constant BOB = address(0xB0B);
    address internal constant CHARLIE = address(0xC4A12);

    function setUp() public {
        token = new ERC20Model(OWNER);
    }

    function _mintAsOwner(address to, uint256 amount) internal {
        vm.prank(OWNER);
        token.mint(to, amount);
    }

    /// Property: constructor_meets_spec
    /// Property: erc20_constructor_meets_spec
    /// Property: constructor_establishes_owner_nonzero
    /// Property: getOwner_meets_spec
    function testProperty_Constructor_SetsOwner() public view {
        assertEq(token.owner(), OWNER, "owner mismatch");
    }

    /// Property: getOwner_preserves_state
    function testProperty_GetOwner_PreservesState(uint256 amount) public {
        amount = bound(amount, 0, 1e30);
        _mintAsOwner(ALICE, amount);

        uint256 supplyBefore = token.totalSupply();
        uint256 aliceBefore = token.balanceOf(ALICE);

        token.owner();

        assertEq(token.totalSupply(), supplyBefore, "totalSupply changed");
        assertEq(token.balanceOf(ALICE), aliceBefore, "balance changed");
    }

    /// Property: erc20_constructor_meets_spec
    /// Property: totalSupply_meets_spec
    function testProperty_Constructor_SetsInitialSupplyZero() public view {
        assertEq(token.totalSupply(), 0, "initial supply must be zero");
    }

    /// Property: getTotalSupply_preserves_state
    function testProperty_GetTotalSupply_PreservesState(uint256 amount) public {
        amount = bound(amount, 0, 1e30);
        _mintAsOwner(ALICE, amount);

        address ownerBefore = token.owner();
        uint256 aliceBefore = token.balanceOf(ALICE);

        token.totalSupply();

        assertEq(token.owner(), ownerBefore, "owner changed");
        assertEq(token.balanceOf(ALICE), aliceBefore, "balance changed");
    }

    /// Property: balanceOf_meets_spec
    function testProperty_BalanceOf_ReturnsMintedBalance(uint256 amount) public {
        amount = bound(amount, 0, 1e30);
        _mintAsOwner(ALICE, amount);
        assertEq(token.balanceOf(ALICE), amount, "balance mismatch");
    }

    /// Property: balanceOf_preserves_state
    function testProperty_BalanceOf_PreservesState(uint256 amount) public {
        amount = bound(amount, 0, 1e30);
        _mintAsOwner(ALICE, amount);

        uint256 supplyBefore = token.totalSupply();
        address ownerBefore = token.owner();

        token.balanceOf(ALICE);

        assertEq(token.totalSupply(), supplyBefore, "totalSupply changed");
        assertEq(token.owner(), ownerBefore, "owner changed");
    }

    /// Property: allowanceOf_meets_spec
    function testProperty_AllowanceOf_ReturnsApprovedAmount(uint256 amount) public {
        vm.prank(ALICE);
        token.approve(BOB, amount);
        assertEq(token.allowanceOf(ALICE, BOB), amount, "allowance mismatch");
    }

    /// Property: allowanceOf_preserves_state
    function testProperty_AllowanceOf_PreservesState(uint256 mintAmount, uint256 allowanceAmount) public {
        mintAmount = bound(mintAmount, 0, 1e30);
        _mintAsOwner(ALICE, mintAmount);

        vm.prank(ALICE);
        token.approve(BOB, allowanceAmount);

        uint256 supplyBefore = token.totalSupply();
        uint256 aliceBefore = token.balanceOf(ALICE);

        token.allowanceOf(ALICE, BOB);

        assertEq(token.totalSupply(), supplyBefore, "totalSupply changed");
        assertEq(token.balanceOf(ALICE), aliceBefore, "balance changed");
    }

    /// Property: approve_meets_spec
    /// Property: approve_is_balance_neutral_holds
    function testProperty_Approve_SetsAllowance_AndPreservesBalances(uint256 minted, uint256 allowanceAmount) public {
        minted = bound(minted, 0, 1e30);
        _mintAsOwner(ALICE, minted);

        uint256 aliceBefore = token.balanceOf(ALICE);
        uint256 bobBefore = token.balanceOf(BOB);
        uint256 supplyBefore = token.totalSupply();

        vm.prank(ALICE);
        token.approve(BOB, allowanceAmount);

        assertEq(token.allowanceOf(ALICE, BOB), allowanceAmount, "allowance not set");
        assertEq(token.balanceOf(ALICE), aliceBefore, "owner balance changed");
        assertEq(token.balanceOf(BOB), bobBefore, "spender balance changed");
        assertEq(token.totalSupply(), supplyBefore, "supply changed");
    }

    /// Property: mint_meets_spec_when_owner
    /// Property: mint_increases_balance_when_owner
    /// Property: mint_increases_supply_when_owner
    function testProperty_Mint_IncreasesRecipientBalance_AndSupply(uint256 amount) public {
        amount = bound(amount, 0, 1e30);

        uint256 balBefore = token.balanceOf(ALICE);
        uint256 supplyBefore = token.totalSupply();

        _mintAsOwner(ALICE, amount);

        assertEq(token.balanceOf(ALICE), balBefore + amount, "recipient balance mismatch");
        assertEq(token.totalSupply(), supplyBefore + amount, "supply mismatch");
    }

    /// Property: mint_meets_spec_when_owner
    /// Property: mint_reverts_when_not_owner
    function testProperty_Mint_RevertsWhenNotOwner(uint256 amount) public {
        vm.prank(ALICE);
        vm.expectRevert(bytes("Caller is not the owner"));
        token.mint(BOB, amount);
    }

    /// Property: transfer_meets_spec_when_sufficient
    /// Property: transfer_decreases_sender_balance_when_sufficient
    /// Property: transfer_increases_recipient_balance_when_sufficient
    function testProperty_Transfer_ConservesBalances_WhenSufficient(uint256 mintAmount, uint256 transferAmount) public {
        mintAmount = bound(mintAmount, 1, 1e30);
        transferAmount = bound(transferAmount, 0, mintAmount);

        _mintAsOwner(ALICE, mintAmount);

        uint256 senderBefore = token.balanceOf(ALICE);
        uint256 recipientBefore = token.balanceOf(BOB);
        uint256 supplyBefore = token.totalSupply();

        vm.prank(ALICE);
        token.transfer(BOB, transferAmount);

        assertEq(token.balanceOf(ALICE), senderBefore - transferAmount, "sender mismatch");
        assertEq(token.balanceOf(BOB), recipientBefore + transferAmount, "recipient mismatch");
        assertEq(token.totalSupply(), supplyBefore, "supply changed");
    }

    /// Property: transfer_meets_spec_when_sufficient
    function testProperty_Transfer_SelfTransferIsNoOp(uint256 mintAmount, uint256 transferAmount) public {
        mintAmount = bound(mintAmount, 1, 1e30);
        transferAmount = bound(transferAmount, 0, mintAmount);

        _mintAsOwner(ALICE, mintAmount);
        uint256 beforeBal = token.balanceOf(ALICE);

        vm.prank(ALICE);
        token.transfer(ALICE, transferAmount);

        assertEq(token.balanceOf(ALICE), beforeBal, "self-transfer changed balance");
    }

    /// Property: transfer_meets_spec_when_sufficient
    /// Property: transfer_reverts_when_insufficient
    function testProperty_Transfer_RevertsOnInsufficientBalance(uint256 mintAmount, uint256 transferAmount) public {
        mintAmount = bound(mintAmount, 0, 1e12);
        transferAmount = bound(transferAmount, mintAmount + 1, mintAmount + 1e12 + 1);

        _mintAsOwner(ALICE, mintAmount);

        vm.prank(ALICE);
        vm.expectRevert(bytes("Insufficient balance"));
        token.transfer(BOB, transferAmount);
    }

    /// Property: transfer_preserves_totalSupply_when_sufficient
    /// Property: transfer_preserves_owner_when_sufficient
    function testProperty_Transfer_PreservesSupplyAndOwner(uint256 mintAmount, uint256 transferAmount) public {
        mintAmount = bound(mintAmount, 1, 1e30);
        transferAmount = bound(transferAmount, 0, mintAmount);

        _mintAsOwner(ALICE, mintAmount);

        uint256 supplyBefore = token.totalSupply();
        address ownerBefore = token.owner();

        vm.prank(ALICE);
        token.transfer(BOB, transferAmount);

        assertEq(token.totalSupply(), supplyBefore, "supply changed");
        assertEq(token.owner(), ownerBefore, "owner changed");
    }

    /// Property: transfer_meets_spec_when_sufficient
    function testProperty_TransferFrom_ConsumesAllowance(uint256 mintAmount, uint256 spendAmount, uint256 allowanceAmount)
        public
    {
        mintAmount = bound(mintAmount, 1, 1e30);
        spendAmount = bound(spendAmount, 0, mintAmount);
        allowanceAmount = bound(allowanceAmount, spendAmount, 1e30);

        _mintAsOwner(ALICE, mintAmount);

        vm.prank(ALICE);
        token.approve(BOB, allowanceAmount);

        vm.prank(BOB);
        token.transferFrom(ALICE, CHARLIE, spendAmount);

        assertEq(token.allowanceOf(ALICE, BOB), allowanceAmount - spendAmount, "allowance not consumed");
    }

    /// Property: transfer_meets_spec_when_sufficient
    function testProperty_TransferFrom_InfiniteAllowanceNotConsumed(uint256 mintAmount, uint256 spendAmount) public {
        mintAmount = bound(mintAmount, 1, 1e30);
        spendAmount = bound(spendAmount, 0, mintAmount);

        _mintAsOwner(ALICE, mintAmount);

        vm.prank(ALICE);
        token.approve(BOB, type(uint256).max);

        vm.prank(BOB);
        token.transferFrom(ALICE, CHARLIE, spendAmount);

        assertEq(token.allowanceOf(ALICE, BOB), type(uint256).max, "infinite allowance should stay max");
    }

    /// Property: transfer_meets_spec_when_sufficient
    function testProperty_TransferFrom_RevertsWhenAllowanceInsufficient(uint256 mintAmount, uint256 spendAmount) public {
        mintAmount = bound(mintAmount, 1, 1e30);
        spendAmount = bound(spendAmount, 1, mintAmount);

        _mintAsOwner(ALICE, mintAmount);

        vm.prank(ALICE);
        token.approve(BOB, spendAmount - 1);

        vm.prank(BOB);
        vm.expectRevert(bytes("Insufficient allowance"));
        token.transferFrom(ALICE, CHARLIE, spendAmount);
    }

    /// Property: transfer_meets_spec_when_sufficient
    function testProperty_TransferFrom_RevertsWhenBalanceInsufficient(uint256 allowanceAmount, uint256 spendAmount) public {
        allowanceAmount = bound(allowanceAmount, 1, 1e30);
        spendAmount = bound(spendAmount, 1, allowanceAmount);

        vm.prank(ALICE);
        token.approve(BOB, allowanceAmount);

        vm.prank(BOB);
        vm.expectRevert(bytes("Insufficient balance"));
        token.transferFrom(ALICE, CHARLIE, spendAmount);
    }

    /// Property: transfer_meets_spec_when_sufficient
    function testProperty_TransferFrom_SelfTransferOnlyUpdatesAllowance(uint256 mintAmount, uint256 spendAmount, uint256 allowanceAmount)
        public
    {
        mintAmount = bound(mintAmount, 1, 1e30);
        spendAmount = bound(spendAmount, 0, mintAmount);
        allowanceAmount = bound(allowanceAmount, spendAmount, 1e30);

        _mintAsOwner(ALICE, mintAmount);
        vm.prank(ALICE);
        token.approve(BOB, allowanceAmount);

        uint256 aliceBefore = token.balanceOf(ALICE);

        vm.prank(BOB);
        token.transferFrom(ALICE, ALICE, spendAmount);

        assertEq(token.balanceOf(ALICE), aliceBefore, "self transferFrom changed balance");
        assertEq(token.allowanceOf(ALICE, BOB), allowanceAmount - spendAmount, "allowance mismatch");
    }
}
