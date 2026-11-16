import Bzip2.Spec.Bwt

/-! What task `bzip2/spec/bwt` provides: the forward transform, the decoder-style inverse, what
an origin pointer of a block is, and which (last column, pointer) pairs the inverse accepts. -/

open Bzip2.Spec.Bwt

#check @bwt
#check @decodeBwt
#check @IsOrigPtr
#check @ValidInput
