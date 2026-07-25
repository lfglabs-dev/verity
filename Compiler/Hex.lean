import Std

namespace Compiler.Hex

def hexCharToNat? (c : Char) : Option Nat :=
  if c.isDigit then
    some (c.toNat - '0'.toNat)
  else if ('a' ≤ c ∧ c ≤ 'f') then
    some (10 + c.toNat - 'a'.toNat)
  else if ('A' ≤ c ∧ c ≤ 'F') then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

def parseHexNat? (s : String) : Option Nat :=
  if s.startsWith "0x" then
    let hexPart := s.drop 2
    if hexPart.isEmpty then
      none
    else
      hexPart.toString.toList.foldl (fun acc c =>
        match acc, hexCharToNat? c with
        | some n, some d => some (n * 16 + d)
        | _, _ => none
      ) (some 0)
  else
    none  -- Only parse as hex if it has "0x" prefix

def stringToNat (s : String) : Nat :=
  s.toList.foldl (fun acc c => acc * 256 + c.toNat) 0

-- Normalize address to lowercase for consistent comparison
def normalizeAddress (addr : String) : String :=
  addr.map Char.toLower

def addressToNat (addr : String) : Nat :=
  match parseHexNat? addr with
  | some n => n % (2^160)
  | none => stringToNat addr % (2^160)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)

/-- Core recursive helper: convert a positive Nat to hex digit chars (big-endian). -/
private def natToHexCore (val : Nat) (acc : List Char) : List Char :=
  if val = 0 then acc
  else natToHexCore (val / 16) (hexDigit (val % 16) :: acc)

/-- Convert a Nat to a zero-padded hex string (e.g. selector → "0x12345678") -/
def natToHex (n : Nat) (digits : Nat := 8) : String :=
  let raw := natToHexCore n []
  let padded := List.replicate (digits - raw.length) '0' ++ raw
  "0x" ++ String.ofList padded

/-- Convert a Nat to a minimal unpadded hex string without prefix (e.g. 255 → "ff"). -/
def natToHexUnpadded (n : Nat) : String :=
  if n = 0 then "0"
  else String.ofList (natToHexCore n [])

end Compiler.Hex
