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

/-- An `if` between two `yield`s is a `yield` of an `if` (so that `for` bodies become folds). -/
theorem ite_pure_yield {β : Type} {m : Type → Type} [Monad m] (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : m (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

/-- `if` with a true condition. -/
theorem ite_of_true {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

/-- `if` with a false condition. -/
theorem ite_of_false {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- `a[n]!` after `set!`. -/
theorem getElem!_set! {α : Type} [Inhabited α] (a : Array α) (i n : Nat) (v : α) :
    (a.set! i v)[n]! = if i = n ∧ i < a.size then v else a[n]! := by
  by_cases hn : n < a.size
  · have hn' : n < (a.set! i v).size := by simpa using hn
    rw [getElem!_pos (a.set! i v) n hn', getElem!_pos a n hn]
    simp only [Array.set!_eq_setIfInBounds]
    by_cases h1 : i = n <;> simp [h1, hn]
  · have hn' : ¬ n < (a.set! i v).size := by simpa using hn
    rw [getElem!_neg (a.set! i v) n hn', getElem!_neg a n hn]
    have : ¬ (i = n ∧ i < a.size) := fun h => hn (h.1 ▸ h.2)
    simp [this]

/-- `a[n]!` after `modify`. -/
theorem getElem!_modify {α : Type} [Inhabited α] (a : Array α) (i n : Nat) (f : α → α) :
    (a.modify i f)[n]! = if i = n ∧ i < a.size then f a[n]! else a[n]! := by
  by_cases hn : n < a.size
  · have hn' : n < (a.modify i f).size := by simpa using hn
    rw [getElem!_pos (a.modify i f) n hn', getElem!_pos a n hn]
    simp only [Array.getElem_modify]
    by_cases h1 : i = n <;> simp [h1, hn]
  · have hn' : ¬ n < (a.modify i f).size := by simpa using hn
    rw [getElem!_neg (a.modify i f) n hn', getElem!_neg a n hn]
    have : ¬ (i = n ∧ i < a.size) := fun h => hn (h.1 ▸ h.2)
    simp [this]

/-- `a[n]!` of a replicated array. -/
theorem getElem!_replicate {α : Type} [Inhabited α] (k n : Nat) (v : α) :
    (Array.replicate k v)[n]! = if n < k then v else default := by
  by_cases hn : n < k
  · have hn' : n < (Array.replicate k v).size := by simpa using hn
    rw [getElem!_pos (Array.replicate k v) n hn']
    simp [hn]
  · have hn' : ¬ n < (Array.replicate k v).size := by simpa using hn
    rw [getElem!_neg (Array.replicate k v) n hn']
    simp [hn]

end Bzip2.Proofs.Huffman.Loops
