import Metamath.Verify

/-!
# Comment lexing in each mode

Executable checks of the book's rules for comments (§4.1.1–4.1.2): a comment may contain only
printable ASCII and the five whitespace bytes, and no `$(` or `$)` inside a longer token.

- `zar`, `sound` and `knife` follow the book (`metamath-knife` accepts exactly these bytes; on a
  byte ≥ 128 it panics, where the `knife` mode reports an error).
- `exe` treats vertical tab as whitespace everywhere, as `metamath.exe` does.
- `permissive` ignores any byte and inner `$(` tokens until a standalone `$)`.

These are tests of concrete runs, not proofs.
-/

namespace Metamath.CommentPolicyCalibration

open Metamath.Verify

def prefixText : String := "$c wff |- $.\n$v p $.\nwp $f wff p $.\nax $a |- p $.\n"

/-- A database ending with the comment `$( a<b>b $)`. -/
def withCommentByte (b : UInt8) : ByteArray :=
  (prefixText ++ "$( a").toUTF8 ++ ByteArray.mk #[b] ++ "b $)\n".toUTF8

/-- A database ending with a comment holding the single word `w`. -/
def withCommentWord (w : String) : ByteArray :=
  (prefixText ++ "$( " ++ w ++ " $)\n").toUTF8

def accepts (config : ModeConfig) (arr : ByteArray) : Bool :=
  (checkBytes arr config).error?.isNone

def acceptedCommentBytes (config : ModeConfig) : List Nat :=
  (List.range 256).filter fun n => accepts config (withCommentByte (UInt8.ofNat n))

/-- Tab, line feed, form feed, carriage return, and printable ASCII (space included). -/
def bookBytes : List Nat := [9, 10, 12, 13] ++ (List.range 95).map (· + 32)

/-! ## Bytes inside a comment -/

#guard acceptedCommentBytes ModeConfig.zar = bookBytes
#guard acceptedCommentBytes ModeConfig.sound = bookBytes
#guard acceptedCommentBytes ModeConfig.knife = bookBytes
#guard acceptedCommentBytes ModeConfig.exe = [9, 10, 11, 12, 13] ++ (List.range 95).map (· + 32)
#guard acceptedCommentBytes ModeConfig.permissive = List.range 256

#guard (checkBytes (withCommentByte 7) {}).parseErrorCode? == some .commentIllegalByte
#guard (checkBytes (withCommentByte 233) ModeConfig.knife).parseErrorCode? ==
  some .commentIllegalByte

/-! ## `$(` and `$)` inside a comment token -/

def delimiterWords : List String := ["x$(y", "x$)y", "$)x", "x$)", "$(x", "x$("]

#guard delimiterWords.all fun w =>
  [ModeConfig.zar, ModeConfig.sound, ModeConfig.knife, ModeConfig.exe].all fun c =>
    !accepts c (withCommentWord w)
#guard delimiterWords.all fun w => accepts ModeConfig.permissive (withCommentWord w)
#guard (checkBytes (withCommentWord "x$(y") {}).parseErrorCode? == some .commentDelimiterInToken
-- A lone `$` is legal comment text in every mode.
#guard [ModeConfig.zar, ModeConfig.knife, ModeConfig.exe, ModeConfig.permissive].all fun c =>
  accepts c (withCommentWord "a$b$$c")
-- Strict and reference modes reject a standalone inner opener.
#guard [ModeConfig.zar, ModeConfig.sound, ModeConfig.knife, ModeConfig.exe].all fun c =>
  (checkBytes (withCommentWord "$(") c).parseErrorCode? == some .nestedCommentDelimiter
-- Permissive comments do not nest: the inner opener is text, and one closer suffices.
#guard accepts ModeConfig.permissive (withCommentWord "$(")
#guard accepts ModeConfig.permissive
  ((prefixText ++ "$( $( ignored $) th $p |- p $= wp ax $.\n").toUTF8)
#guard ((checkBytes
  ((prefixText ++ "$( $( ignored $) th $p |- p $= wp ax $.\n").toUTF8)
  ModeConfig.permissive).find? "th").isSome
-- Ignoring contents neither permits an unterminated comment nor declares hidden axioms.
#guard !accepts ModeConfig.permissive ((prefixText ++ "$( $( unfinished").toUTF8)
#guard ((checkBytes (withCommentWord "$( hidden $a |- p $.")
  ModeConfig.permissive).find? "hidden").isNone

/-! ## Vertical tab separates tokens in `exe` and `permissive` -/

def vtBetweenSymbols : ByteArray :=
  "$c a".toUTF8 ++ ByteArray.mk #[11] ++ "b $.\n".toUTF8

#guard accepts ModeConfig.exe vtBetweenSymbols
#guard ((checkBytes vtBetweenSymbols ModeConfig.exe).find? "b").isSome
#guard accepts ModeConfig.permissive vtBetweenSymbols
#guard [ModeConfig.zar, ModeConfig.sound, ModeConfig.knife].all fun c =>
  !accepts c vtBetweenSymbols

/-! ## Terminal escapes after an axiom

The escape codes erase the axiom line on a terminal; the axiom is real and the proof uses it. Every
mode but `permissive` rejects the file. -/

def hiddenAxiom : ByteArray :=
  "$c wff |- F $.\n$v p $.\nwp $f wff p $.\nevil $a |- F $. $( ".toUTF8 ++
    ByteArray.mk #[27, 91, 50, 75, 27, 91, 71] ++
    "$( see the axioms above $)\nth $p |- F $= evil $.\n".toUTF8

#guard [ModeConfig.zar, ModeConfig.sound, ModeConfig.knife, ModeConfig.exe].all fun c =>
  !accepts c hiddenAxiom
#guard accepts ModeConfig.permissive hiddenAxiom
#guard ((checkBytes hiddenAxiom ModeConfig.permissive).find? "evil").isSome

end Metamath.CommentPolicyCalibration
