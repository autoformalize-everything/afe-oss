import Mathlib.Data.List.Basic

/-!
# Huffman proofs: reasoning about the oracle's loops

The oracle is written with `for` and `while` in `Id.run do` blocks. A `for` over a range is a
left fold over `List.range'`; a `while` (`Lean.Loop.forIn`) unfolds one step at a time
(`Lean.Loop.forIn_eq_of_monadTail`), which tells nothing about a loop that never ends. So the rule
for `while` here, `forIn_loop_rel`, asks for a measure that decreases on every iteration: a
statement about the result of a loop is a statement about a loop proved to end.
-/

namespace Bzip2.Proofs.Huffman.Loops

/-- One unfolding step of a `while`/`repeat` loop in `Id`. -/
theorem forIn_loop_unfold {β : Type} (b : β) (f : Unit → β → Id (ForInStep β)) :
    forIn Lean.Loop.mk b f = (match f () b with
      | .done v => v
      | .yield v => forIn Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail (m := Id) (l := Lean.Loop.mk) (b := b) (f := f)

/-- Rule for `while` loops in `Id`: `R b r` says that the loop started at `b` may return `r`.
It holds when `R b v` for every step that stops with `v`, and for every step that continues
with `v` such that `P v` holds, a measure decreases, and `R v r` gives `R b r`. -/
theorem forIn_loop_rel {β : Type} (P : β → Prop) (R : β → β → Prop) (μ : β → Nat)
    (f : Unit → β → Id (ForInStep β))
    (hdone : ∀ b v, P b → f () b = .done v → R b v)
    (hyield : ∀ b v, P b → f () b = .yield v → P v ∧ μ v < μ b ∧ ∀ r, R v r → R b r) :
    ∀ b, P b → R b (forIn Lean.Loop.mk b f) := by
  intro b
  induction h : μ b using Nat.strongRecOn generalizing b with
  | _ m ih =>
    intro hb
    rw [forIn_loop_unfold]
    cases hfb : f () b with
    | done v => exact hdone b v hb hfb
    | yield v =>
      obtain ⟨hv, hlt, hR⟩ := hyield b v hb hfb
      exact hR _ (ih (μ v) (h ▸ hlt) v rfl hv)

end Bzip2.Proofs.Huffman.Loops
