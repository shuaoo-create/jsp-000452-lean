import RegularBipartitePick
import Mathlib.Data.Finite.Sum

namespace JSP452Audit.StarHost
namespace LayerConstruction

private theorem card_sum_sub {A B : Type*} [Finite A] [Finite B] (P : A ⊕ B → Prop) :
    Nat.card {x // P x} = Nat.card {a // P (.inl a)} + Nat.card {b // P (.inr b)} :=
  (Nat.card_congr (Equiv.subtypeSum (p := P))).trans Nat.card_sum

private theorem card_fixed_first {A B : Type*} (a : A) :
    Nat.card {x : A × B // x.1 = a} = Nat.card B := by
  apply Nat.card_congr
  exact { toFun := fun x => x.val.2, invFun := fun b => ⟨(a,b),rfl⟩,
          left_inv := by rintro ⟨⟨z,b⟩,rfl⟩; rfl, right_inv := fun _ => rfl }

private abbrev Tickets (O V : Type*) (k : ℕ) := O ⊕ (V × Fin k)
private abbrev owner {O V : Type*} (f : O → V) : O ⊕ V → V := Sum.elim f id
private abbrev ticketSlot {O V : Type*} {k : ℕ} : Tickets O V k → O ⊕ V :=
  Sum.elim Sum.inl (fun z => Sum.inr z.1)

variable {O N V : Type*} [Finite O] [Finite N] [Finite V]

/-- Allocate one new incidence to each old-edge slot and k to the extra slot per vertex. -/
private theorem layout (old : O → V) (new : N → V) (k : ℕ)
    (gap : ∀ v, Nat.card {e // new e = v} = Nat.card {e // old e = v} + k) :
    ∃ h : N ≃ Tickets O V k, ∀ e, owner old (ticketSlot (h e)) = new e := by
  let tag : Tickets O V k → V := owner old ∘ ticketSlot
  have size (v : V) : Nat.card {t // tag t = v} = Nat.card {e // old e = v} + k := by
    rw [card_sum_sub (fun t => tag t = v)]
    simp only [tag,Function.comp_apply,ticketSlot,owner,Sum.elim_inl,Sum.elim_inr,id_eq,
      card_fixed_first,Nat.card_fin]
  let iso (v : V) : {e // new e = v} ≃ {t // tag t = v} := by
    classical
    let _ := Fintype.ofFinite {e // new e = v}
    let _ := Fintype.ofFinite {t : Tickets O V k // tag t = v}
    exact Fintype.equivOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using (gap v).trans (size v).symm)
  exact ⟨Equiv.ofFiberEquiv iso, Equiv.ofFiberEquiv_map iso⟩

/-- Old IDs have k−1 copies sharing both endpoint slots. New IDs occur once. -/
private abbrev Jobs (O N : Type*) (k : ℕ) := (O × Fin (k-1)) ⊕ N
private abbrev slot {k : ℕ} (h : N ≃ Tickets O V k) : Jobs O N k → O ⊕ V :=
  Sum.elim (fun x => Sum.inl x.1) (fun x => ticketSlot (h x))
private abbrev raw {k : ℕ} : Jobs O N k → O ⊕ N :=
  Sum.elim (fun x => Sum.inl x.1) Sum.inr

private theorem slot_regular {k : ℕ} (hk : 0<k) (h : N ≃ Tickets O V k) (c : O ⊕ V) :
    Nat.card {e // slot h e = c} = k := by
  rw [card_sum_sub (fun e => slot h e = c)]
  change Nat.card {x : O × Fin (k-1) // Sum.inl x.1 = c} +
    Nat.card {e : N // ticketSlot (h e) = c} = k
  rw [Nat.card_congr (Equiv.subtypeEquiv (p := fun e : N => ticketSlot (h e) = c)
    (q := fun t => ticketSlot t = c) h (fun _ => Iff.rfl)),card_sum_sub (fun t : Tickets O V k => ticketSlot t = c)]
  cases c with
  | inl o =>
    simp [ticketSlot, card_fixed_first]
    omega
  | inr v =>
    simp [ticketSlot, card_fixed_first]

private theorem owner_fiber (f : O → V) (v : V) :
    Nat.card {c : O ⊕ V // owner f c = v} = Nat.card {o // f o = v} + 1 := by
  rw [card_sum_sub (fun c => owner f c = v)]
  simp [owner]


private abbrev rawSlot {k : ℕ} (h : N ≃ Tickets O V k) : O ⊕ N → O ⊕ V :=
  Sum.elim Sum.inl (fun e => ticketSlot (h e))

omit [Finite O] [Finite N] [Finite V] in
private theorem slot_raw {k : ℕ} (h : N ≃ Tickets O V k) (e : Jobs O N k) :
    rawSlot h (raw e) = slot h e := by cases e <;> rfl

omit [Finite O] [Finite N] [Finite V] in
private theorem owner_raw {k : ℕ} (old : O → V) (new : N → V) (h : N ≃ Tickets O V k)
    (valid : ∀ n, owner old (ticketSlot (h n)) = new n) (e : Jobs O N k) :
    owner old (slot h e) = Sum.elim old new (raw e) := by
  cases e with
  | inl x => rfl
  | inr x => exact valid x

private theorem selected_count (old : O → V) (new : N → V)
    (sel : O ⊕ V → O ⊕ N) (inj : Function.Injective sel) (matchSlot : (O ⊕ V) ≃ (O ⊕ V))
    (compatible : ∀ c, owner old (matchSlot c) = Sum.elim old new (sel c)) (v : V) :
    Nat.card {o : O // Sum.inl o ∈ Set.range sel ∧ old o = v} +
    Nat.card {n : N // Sum.inr n ∈ Set.range sel ∧ new n = v} =
      Nat.card {o : O // old o = v} + 1 := by
  let f : O ⊕ N → V := Sum.elim old new
  let source := {c : O ⊕ V // f (sel c) = v}
  let chosen := {e : O ⊕ N // e ∈ Set.range sel ∧ f e = v}
  let toChosen : source ≃ chosen :=
    ((Equiv.ofInjective sel inj).subtypeEquiv (p := fun c => f (sel c) = v)
      (q := fun e => f e.val = v) (fun _ => Iff.rfl)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ Set.range sel) (fun e => f e = v))
  let toSlots : source ≃ {c : O ⊕ V // owner old c = v} :=
    matchSlot.subtypeEquiv (fun c => by
      change f (sel c) = v ↔ owner old (matchSlot c) = v
      rw [compatible c])
  calc
    _ = Nat.card chosen := (card_sum_sub (fun e => e ∈ Set.range sel ∧ f e = v)).symm
    _ = Nat.card {c : O ⊕ V // owner old c = v} := Nat.card_congr (toChosen.symm.trans toSlots)
    _ = _ := owner_fiber old v

end LayerConstruction

open LayerConstruction

/-- Project one regular bipartite layer of cloned edge IDs back to the original old
and new directed edges. Each vertex gains one incidence at each of its two ends.
The old and new edge types are separate; each original ID is selected at most once. -/
theorem directed_factor_layer {O N V : Type*} [Finite O] [Finite N] [Finite V]
    (srcO dstO : O → V) (srcN dstN : N → V) (k : ℕ) (pos : 0 < k)
    (hs : ∀ v, Nat.card {e : N // srcN e = v} = Nat.card {e : O // srcO e = v} + k)
    (ht : ∀ v, Nat.card {e : N // dstN e = v} = Nat.card {e : O // dstO e = v} + k) :
    ∃ (SO : Set O) (SN : Set N),
      (∀ v, Nat.card {e : O // e ∈ SO ∧ srcO e = v} +
        Nat.card {e : N // e ∈ SN ∧ srcN e = v} = Nat.card {e : O // srcO e = v} + 1) ∧
      (∀ v, Nat.card {e : O // e ∈ SO ∧ dstO e = v} +
        Nat.card {e : N // e ∈ SN ∧ dstN e = v} = Nat.card {e : O // dstO e = v} + 1) := by
  obtain ⟨s,vs⟩ := layout srcO srcN k hs
  obtain ⟨t,vt⟩ := layout dstO dstN k ht
  obtain ⟨pick,source,matchTarget⟩ := regular_bipartite_representatives
    (slot s) (slot t) k pos (slot_regular pos s) (slot_regular pos t)
  let sel : O ⊕ V → O ⊕ N := raw ∘ pick
  have inject : Function.Injective sel := by
    intro x y eq
    have same := congrArg (rawSlot s) eq
    change rawSlot s (raw (pick x)) = rawSlot s (raw (pick y)) at same
    simpa only [slot_raw,source] using same
  refine ⟨{o | Sum.inl o ∈ Set.range sel},{n | Sum.inr n ∈ Set.range sel},?_,?_⟩
  · apply selected_count srcO srcN sel inject (Equiv.refl _)
    intro c
    change owner srcO c = Sum.elim srcO srcN (raw (pick c))
    exact (congrArg (owner srcO) (source c).symm).trans (owner_raw srcO srcN s vs (pick c))
  · apply selected_count dstO dstN sel inject (Equiv.ofBijective (slot t ∘ pick) matchTarget)
    intro c
    exact owner_raw dstO dstN t vt (pick c)

#print axioms directed_factor_layer
end JSP452Audit.StarHost
