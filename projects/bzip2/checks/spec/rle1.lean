import Bzip2.Spec.Rle1

/-! What task `bzip2/spec/rle1` provides. -/

open Bzip2.Spec.Rle1

#check (decodeRle1 : List UInt8 → List UInt8)
#check (encodeRle1 : List UInt8 → List UInt8)
