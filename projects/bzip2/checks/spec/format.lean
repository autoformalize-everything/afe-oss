import Bzip2.Spec.Format

/-! What task `bzip2/spec/format` provides. -/

open Bzip2.Spec.Format

#check (Decodes : List UInt8 → List UInt8 → Prop)
#check @ValidCompression
