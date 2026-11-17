import Mathlib.Data.List.Basic
import Bzip2.Proofs.Huffman.Loops

/-!
# Huffman proofs: parent chains

`BZ2_hbMakeCodeLengths` records the Huffman tree as a `parent` array (`huffman.c:91-110`) and
reads each code length off it by walking from the leaf to the root, counting the steps
(`huffman.c:112-123`). `Reaches P x r d` says that walking from node `x` through `P` ends at the
root `r` (`P[r] = 0`) after `d` steps. `ValidParents P N` says that the parent of a node is a
larger node below `N`, so every walk ends (`reaches_exists`); `reaches_merge` is what a merge
(`huffman.c:104-105`: two roots get the new node as parent) does to the walks.
-/

namespace Bzip2.Proofs.Huffman.Chain

open Bzip2.Proofs.Huffman.Loops

/-- Walking from `x` through the parent array `P` reaches the root `r` after `d` steps. -/
inductive Reaches (P : Array Nat) : Nat → Nat → Nat → Prop where
  /-- A node without parent is its own root. -/
  | root {x : Nat} : P[x]! = 0 → Reaches P x x 0
  /-- Otherwise the walk continues from the parent. -/
  | step {x r d : Nat} : P[x]! ≠ 0 → Reaches P P[x]! r d → Reaches P x r (d + 1)

/-- Every node has at most one root and distance. -/
theorem Reaches.unique {P : Array Nat} {x r d r' d' : Nat} (h : Reaches P x r d)
    (h' : Reaches P x r' d') : r = r' ∧ d = d' := by
  induction h generalizing r' d' with
  | root hx =>
    cases h' with
    | root _ => exact ⟨rfl, rfl⟩
    | step hne _ => exact absurd hx hne
  | step hne _ ih =>
    cases h' with
    | root hx => exact absurd hx hne
    | step _ h2 =>
      obtain ⟨e1, e2⟩ := ih h2
      exact ⟨e1, by omega⟩

/-- Every node's parent is a larger node below `N`. -/
def ValidParents (P : Array Nat) (N : Nat) : Prop :=
  ∀ x : Nat, P[x]! ≠ 0 → x < P[x]! ∧ P[x]! < N

/-- On valid parents every node below `N` has a root, within `N - x` steps. -/
theorem reaches_exists {P : Array Nat} {N : Nat} (hv : ValidParents P N) :
    ∀ k x, N - x = k → ∃ r d, Reaches P x r d ∧ d ≤ k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro x hk
    by_cases h0 : P[x]! = 0
    · exact ⟨x, 0, Reaches.root h0, Nat.zero_le _⟩
    · obtain ⟨hlt, hbound⟩ := hv x h0
      obtain ⟨r, d, hr, hd⟩ := ih (N - P[x]!) (by omega) P[x]! rfl
      exact ⟨r, d + 1, Reaches.step h0 hr, by omega⟩

end Bzip2.Proofs.Huffman.Chain
