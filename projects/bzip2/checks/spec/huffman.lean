import Bzip2.Spec.Huffman

/-! What task `bzip2/spec/huffman` provides: the code assigned to a symbol by a table of
lengths, and decoding one symbol from bits as the C decoder does. -/

open Bzip2.Spec.Huffman

#check @codeword
#check @decodeSym
