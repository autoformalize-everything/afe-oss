import Mathlib.Data.List.Basic

/-!
# Huffman proofs: the binary heap of `BZ2_hbMakeCodeLengths`, definitions

The compressor keeps the roots of the partial Huffman forest in a binary min-heap
(`huffman.c:33-59`, `UPHEAP` and `DOWNHEAP`): `heap[1 .. nHeap]` holds node numbers, ordered by
the key `weight[heap[i]]`, with the parent of position `i` at `i / 2`. This module states what
the proofs of `upHeap` and `downHeap` (`Heap.Up`, `Heap.Down`) and of the merge loop speak
about:

* `key heap weight i` is the key at position `i`;
* `HeapOrd heap weight n`: positions `1 .. n` are in heap order (every position `i ≥ 2` has a key
  at least that of its parent `i / 2`);
* `cnt heap n x`: how many of the positions `1 .. n` hold the node `x`. Equal counts for every `x`
  say that the positions `1 .. n` hold the same nodes with the same multiplicities.
-/

namespace Bzip2.Proofs.Huffman.Heap.Defs

/-- The key of heap position `i`: the weight of the node stored there. -/
def key (heap weight : Array Nat) (i : Nat) : Nat := weight[heap[i]!]!

/-- Positions `1 .. n` of `heap` are in heap order for the keys given by `weight`: every position
`i` with `2 ≤ i ≤ n` has a key at least that of its parent `i / 2`. -/
def HeapOrd (heap weight : Array Nat) (n : Nat) : Prop :=
  ∀ i, 2 ≤ i → i ≤ n → key heap weight (i / 2) ≤ key heap weight i

/-- The number of the positions `1 .. n` of `heap` that hold the node `x`. -/
def cnt (heap : Array Nat) (n x : Nat) : Nat :=
  ((List.range' 1 n).filter (fun i => heap[i]! == x)).length

end Bzip2.Proofs.Huffman.Heap.Defs
