/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Utils.FromString

/-!
# Decimal notation for `Float`

A `Float` has to survive the trip through a database as the exact value it was, and neither of the
two conversions Lean offers does that. `Float.toString` prints six digits after the point, so
`toString (1e-7 : Float)` is `"0.000000"` and every value below that renders as zero; `Lean.toJson`
goes through the same printer and is lossy the same way.

`Float.toDecimalString` prints the seventeen significant digits of the *exact* binary value
instead, which is the shortest precision at which every double round-trips. It works in exact `Nat`
arithmetic: `Float.frExp x` gives `m ∈ [0.5, 1)` and `e` with `x = m · 2 ^ e`, `m · 2 ^ 53` is an
integer (a double has 53 bits of mantissa, and scaling by a power of two is exact), and from that
integer and the exponent the decimal digits are a long division carried out on `Nat`s.

`Float.ofDecimalString?` reads back what that prints and what the two backends print for a
floating-point column — `0.1`, `-3`, `1e-07`, `1.0e+20`, `1E5`, `.5` — building the value with
`Float.ofScientific`, which is correctly rounded.

NaN and the infinities have no SQL literal, so `Float.toDecimalString?` reports them as `none`;
`Float.toDecimalString` falls back to Lean's own spelling of them, which is for a human to read and
not for a database to parse.
-/

namespace Db.Utils

/-- `2 ^ 53`, the scale at which the mantissa of a double is an integer. -/
private def twoPow53 : Float := 9007199254740992.0

/--
The decimal digits of a *positive, finite* float, rounded to `prec` significant digits.

Returns the digit string — exactly `prec` characters, the first of them not `'0'` — together with
the exponent `k` for which the value is `0.<digits> · 10 ^ k`.
-/
private def sigDigits (x : Float) (prec : Nat) : String × Int := Id.run do
  let (m, e) := x.frExp
  -- `m ∈ [0.5, 1)`, so `m * 2 ^ 53` is an integer in `[2 ^ 52, 2 ^ 53)`, exactly representable and
  -- exactly truncated. This holds for a subnormal too: `frExp` normalises it into that range.
  let mantissa : Nat := (m * twoPow53).toUInt64.toNat
  let twoExp : Int := e - 53
  -- `x = num / den`, exactly.
  let (num, den) : Nat × Nat :=
    if twoExp ≥ 0 then (mantissa <<< twoExp.toNat, 1) else (mantissa, 1 <<< (-twoExp).toNat)
  -- `k` is the smallest exponent with `num / den < 10 ^ k`. The difference of the decimal lengths
  -- is within one of it, so one comparison decides which.
  let ltPow : Int → Bool := fun k =>
    if k ≥ 0 then num < den * 10 ^ k.toNat else num * 10 ^ (-k).toNat < den
  let k₀ : Int := (toString num).length - (toString den).length
  let mut k : Int := if ltPow k₀ then k₀ else k₀ + 1
  -- The digits are `num / den * 10 ^ (prec - k)`, rounded to the nearest integer.
  let scale : Int := prec - k
  let (n, d) : Nat × Nat :=
    if scale ≥ 0 then (num * 10 ^ scale.toNat, den) else (num, den * 10 ^ (-scale).toNat)
  let mut q := n / d
  if 2 * (n % d) ≥ d then
    q := q + 1
  -- Rounding up may carry into an extra digit, as `9.99…` does.
  if q ≥ 10 ^ prec then
    q := 10 ^ (prec - 1)
    k := k + 1
  return (toString q, k)

/-- The digits with their trailing zeros removed. `digits` has a non-zero leading digit, so this
never empties it. -/
private def stripTrailingZeros (digits : String) : List Char :=
  (digits.toList.reverse.dropWhile (· == '0')).reverse

/--
`x` in decimal notation, at seventeen significant digits of the exact binary value, so that reading
the result back gives `x` again.

There is always a digit on either side of the point, and never a bare integer: `4.0`, not `4`, so
that a reader of the generated SQL — and the database parsing it — sees a floating-point literal
rather than an integer one. Very large and very small magnitudes come out in exponent notation
(`1.0e20`, `1.0e-7`).

`none` for NaN and the infinities, which have no literal in either dialect.
-/
def _root_.Float.toDecimalString? (x : Float) : Option String :=
  if !x.isFinite then
    none
  else if x == 0 then
    -- `0 == -0`, so the sign of a zero is only in its bits.
    some (if x.toBits >>> 63 == 1 then "-0.0" else "0.0")
  else
    let neg := x < 0
    let (digits, k) := sigDigits (if neg then -x else x) 17
    let s := stripTrailingZeros digits
    let len : Int := s.length
    let body : String :=
      if k > 17 || k ≤ -4 then
        -- Exponent notation, normalised to one digit before the point.
        let frac := if s.length > 1 then String.ofList (s.drop 1) else "0"
        s!"{String.ofList (s.take 1)}.{frac}e{k - 1}"
      else if k ≤ 0 then
        "0." ++ String.ofList (List.replicate (-k).toNat '0') ++ String.ofList s
      else if k ≥ len then
        String.ofList s ++ String.ofList (List.replicate (k - len).toNat '0') ++ ".0"
      else
        String.ofList (s.take k.toNat) ++ "." ++ String.ofList (s.drop k.toNat)
    some (if neg then "-" ++ body else body)

/--
`x` in decimal notation, falling back to Lean's own spelling for NaN and the infinities, which have
no decimal notation. Use `Float.toDecimalString?` where the result has to be a literal a database
will read.
-/
def _root_.Float.toDecimalString (x : Float) : String :=
  (Float.toDecimalString? x).getD (toString x)

/-- Split a character list at the first occurrence of `e` or `E`, dropping it. -/
private def splitExponent (cs : List Char) : List Char × Option (List Char) :=
  match cs.findIdx? (fun c => c == 'e' || c == 'E') with
  | some i => (cs.take i, some (cs.drop (i + 1)))
  | none => (cs, none)

/-- Split a character list at the first `.`, dropping it. -/
private def splitPoint (cs : List Char) : List Char × List Char :=
  match cs.findIdx? (· == '.') with
  | some i => (cs.take i, cs.drop (i + 1))
  | none => (cs, [])

/-- An optional leading sign, and the rest. -/
private def splitSign (cs : List Char) : Bool × List Char :=
  match cs with
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | _ => (false, cs)

/--
Read a decimal number as the backends print one for a floating-point column: an optional sign, then
digits with an optional point (on either side of which the digits may be missing, so `.5` and `3.`
are both accepted) and an optional exponent, `e` or `E`, itself optionally signed.

`Infinity`, `inf` and `NaN` — what the two backends print for a stored non-finite value — are
accepted too, in any case, so that reading such a row reports the value rather than failing. They
have no literal to write them back with; see `Float.toDecimalString?`.
-/
def _root_.Float.ofDecimalString? (input : String) : Option Float := do
  let trimmed := input.trimAscii.toString.toList
  if trimmed.isEmpty then failure
  let (neg, cs) := splitSign trimmed
  let signed (v : Float) : Float := if neg then -v else v
  match String.ofList (cs.map Char.toLower) with
  | "inf" | "infinity" => return signed (1.0 / 0.0)
  | "nan" => return 0.0 / 0.0
  | _ =>
  let (mantissa, exponent?) := splitExponent cs
  let exp : Int ← match exponent? with
    | none => pure 0
    | some e =>
      let (eneg, digits) := splitSign e
      -- A ten-million-fold exponent is not a number anyone stored; refusing it keeps the `Nat`
      -- arithmetic below bounded.
      if digits.isEmpty || !digits.all Char.isDigit || digits.length > 7 then failure
      let n ← (String.ofList digits).toNat?
      pure (if eneg then -(n : Int) else (n : Int))
  let (whole, frac) := splitPoint mantissa
  if !whole.all Char.isDigit || !frac.all Char.isDigit then failure
  if whole.isEmpty && frac.isEmpty then failure
  let digits := whole ++ frac
  let value ← (String.ofList digits).toNat?
  if value == 0 then return signed 0.0
  let exp10 : Int := exp - frac.length
  -- The decimal exponent of the value, give or take one. Outside the range of a double there is
  -- nothing to compute: saturate rather than build a thousand-digit `Nat`.
  let magnitude : Int := exp10 + digits.length
  if magnitude > 320 then return signed (1.0 / 0.0)
  if magnitude < -350 then return signed 0.0
  return signed <|
    if exp10 ≥ 0 then Float.ofScientific value false exp10.toNat
    else Float.ofScientific value true (-exp10).toNat

end Db.Utils

instance : FromString Float where
  fromString := Float.ofDecimalString?
