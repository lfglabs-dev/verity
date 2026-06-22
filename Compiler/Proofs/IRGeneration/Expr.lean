/- 
  Concrete IR fixtures consumed by semantic-bridge and end-to-end proofs.
-/

import Compiler.Constants
import Compiler.IR
import Compiler.Yul.Ast

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Constants
open Compiler.Yul

/-- Concrete IR contract for SimpleStorage. -/
def simpleStorageIRContract : IRContract :=
  { name := "SimpleStorage"
    deploy := []
    functions := [
      { name := "store"
        selector := 0x6057361d
        params := [{ name := "value", ty := IRType.uint256 }]
        ret := IRType.unit
        body := [
          YulStmt.let_ "value" (YulExpr.call "calldataload" [YulExpr.lit 4]),
          YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "value"]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "retrieve"
        selector := 0x2e64cec1
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 0]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

/-- Concrete IR contract for Counter. -/
def counterIRContract : IRContract :=
  { name := "Counter"
    deploy := []
    functions := [
      { name := "increment"
        selector := 0xd09de08a
        params := []
        ret := IRType.unit
        body := [
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.lit 0,
            YulExpr.call "add" [YulExpr.call "sload" [YulExpr.lit 0], YulExpr.lit (1 % (2 ^ 256))]
          ]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "decrement"
        selector := 0x2baeceb7
        params := []
        ret := IRType.unit
        body := [
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.lit 0,
            YulExpr.call "sub" [YulExpr.call "sload" [YulExpr.lit 0], YulExpr.lit (1 % (2 ^ 256))]
          ]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "getCount"
        selector := 0xa87d942c
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 0]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

/-- Minimal concrete ERC-4626-Vault IR fixture exposing the `totalAssets()`
view function. Same IR shape as `simpleStorageIRContract.retrieve` but with
the ERC-4626 standard `totalAssets()` selector (`0x01e1d114`). Used by the
G3 native theorem in `Contracts/Vault/Proofs/Native.lean`. -/
def vaultMinimalIRContract : IRContract :=
  { name := "VaultMinimal"
    deploy := []
    functions := [
      { name := "totalAssets"
        selector := 0x01e1d114
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore"
            [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 0]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

/-- Minimal concrete ERC-20 IR fixture exposing the `totalSupply()` view
function. Same IR shape as `simpleStorageIRContract.retrieve` but with the
ERC-20 standard `totalSupply()` selector (`0x18160ddd`) and storage at the
canonical totalSupply slot 1. Used by the G3 native theorem in
`Contracts/ERC20/Proofs/Native.lean`. -/
def erc20MinimalIRContract : IRContract :=
  { name := "ERC20Minimal"
    deploy := []
    functions := [
      { name := "totalSupply"
        selector := 0x18160ddd
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore"
            [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 1]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

def safeCounterOverflowRevert : List YulStmt :=
  [
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit 21]),
    YulStmt.exprStmt (YulExpr.call "mstore" [
      YulExpr.lit 68,
      YulExpr.hex 0x4f766572666c6f7720696e20696e6372656d656e740000000000000000000000
    ]),
    YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 100])
  ]

def safeCounterUnderflowRevert : List YulStmt :=
  [
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit 22]),
    YulStmt.exprStmt (YulExpr.call "mstore" [
      YulExpr.lit 68,
      YulExpr.hex 0x556e646572666c6f7720696e2064656372656d656e7400000000000000000000
    ]),
    YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 100])
  ]

def insufficientBalanceRevert : List YulStmt :=
  [
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit 20]),
    YulStmt.exprStmt (YulExpr.call "mstore" [
      YulExpr.lit 68,
      YulExpr.hex 0x496e73756666696369656e742062616c616e6365000000000000000000000000
    ]),
    YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 100])
  ]

/-- Concrete IR contract for SafeCounter. -/
def safeCounterIRContract : IRContract :=
  { name := "SafeCounter"
    deploy := []
    functions := [
      { name := "increment"
        selector := 0xd09de08a
        params := []
        ret := IRType.unit
        body := [
          YulStmt.let_ "count" (YulExpr.call "sload" [YulExpr.lit 0]),
          YulStmt.let_ "newCount" (YulExpr.call "add" [YulExpr.ident "count", YulExpr.lit (1 % (2 ^ 256))]),
          YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.call "gt" [YulExpr.ident "newCount", YulExpr.ident "count"]])
            safeCounterOverflowRevert,
          YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "newCount"]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "decrement"
        selector := 0x2baeceb7
        params := []
        ret := IRType.unit
        body := [
          YulStmt.let_ "count" (YulExpr.call "sload" [YulExpr.lit 0]),
          YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident "count", YulExpr.lit (1 % (2 ^ 256))])
            safeCounterUnderflowRevert,
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.lit 0,
            YulExpr.call "sub" [YulExpr.ident "count", YulExpr.lit (1 % (2 ^ 256))]
          ]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "getCount"
        selector := 0xa87d942c
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 0]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

def ownedNotOwnerRevert : List YulStmt :=
  [
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit 9]),
    YulStmt.exprStmt (YulExpr.call "mstore" [
      YulExpr.lit 68,
      YulExpr.hex 0x4e6f74206f776e65720000000000000000000000000000000000000000000000
    ]),
    YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 100])
  ]

/-- Concrete IR contract for Owned. -/
def ownedIRContract : IRContract :=
  { name := "Owned"
    deploy := [
      YulStmt.let_ "argsOffset" (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.lit 32]),
      YulStmt.exprStmt (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.lit 32]),
      YulStmt.let_ "arg0" (YulExpr.call "and" [YulExpr.call "mload" [YulExpr.lit 0], YulExpr.hex addressMask]),
      YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "arg0"])
    ]
    functions := [
      { name := "transferOwnership"
        selector := 0xf2fde38b
        params := [{ name := "newOwner", ty := IRType.address }]
        ret := IRType.unit
        body := [
          YulStmt.let_ "newOwner" (YulExpr.call "and" [
            YulExpr.call "calldataload" [YulExpr.lit 4],
            YulExpr.hex addressMask
          ]),
          YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.call "eq" [YulExpr.call "caller" [], YulExpr.call "sload" [YulExpr.lit 0]]])
            ownedNotOwnerRevert,
          YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "newOwner"]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "getOwner"
        selector := 0x893d20e8
        params := []
        ret := IRType.address
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 0]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

/-- Concrete IR contract for OwnedCounter. -/
def ownedCounterIRContract : IRContract :=
  { name := "OwnedCounter"
    deploy := [
      YulStmt.let_ "argsOffset" (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.lit 32]),
      YulStmt.exprStmt (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.lit 32]),
      YulStmt.let_ "arg0" (YulExpr.call "and" [YulExpr.call "mload" [YulExpr.lit 0], YulExpr.hex addressMask]),
      YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "arg0"])
    ]
    functions := [
      { name := "increment"
        selector := 0xd09de08a
        params := []
        ret := IRType.unit
        body := [
          YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.call "eq" [YulExpr.call "caller" [], YulExpr.call "sload" [YulExpr.lit 0]]])
            ownedNotOwnerRevert,
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.lit 1,
            YulExpr.call "add" [YulExpr.call "sload" [YulExpr.lit 1], YulExpr.lit 1]
          ]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "decrement"
        selector := 0x2baeceb7
        params := []
        ret := IRType.unit
        body := [
          YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.call "eq" [YulExpr.call "caller" [], YulExpr.call "sload" [YulExpr.lit 0]]])
            ownedNotOwnerRevert,
          YulStmt.exprStmt (YulExpr.call "sstore" [
            YulExpr.lit 1,
            YulExpr.call "sub" [YulExpr.call "sload" [YulExpr.lit 1], YulExpr.lit 1]
          ]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      },
      { name := "getCount"
        selector := 0xa87d942c
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 1]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      },
      { name := "getOwner"
        selector := 0x893d20e8
        params := []
        ret := IRType.address
        body := [
          YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 0]]),
          YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      },
      { name := "transferOwnership"
        selector := 0xf2fde38b
        params := [{ name := "newOwner", ty := IRType.address }]
        ret := IRType.unit
        body := [
          YulStmt.let_ "newOwner" (YulExpr.call "and" [
            YulExpr.call "calldataload" [YulExpr.lit 4],
            YulExpr.hex addressMask
          ]),
          YulStmt.if_
            (YulExpr.call "iszero" [YulExpr.call "eq" [YulExpr.call "caller" [], YulExpr.call "sload" [YulExpr.lit 0]]])
            ownedNotOwnerRevert,
          YulStmt.exprStmt (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "newOwner"]),
          YulStmt.exprStmt (YulExpr.call "stop" [])
        ]
      }
    ]
    usesMapping := false }

end Compiler.Proofs.IRGeneration
