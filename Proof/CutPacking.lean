import BlockColor
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A subfamily of a real monochromatic copy landing in a single pullback
has size at most the capacity of that pullback. -/
theorem subfamily_card_of_block {I J X Z : Type*} [Finite J] [Finite Z]
    {n : I → ℕ} {R : SimpleGraph X} (f : (forest n).Copy R)
    (j : J ↪ I) (incl : Z → X) {p : ℕ}
    (localCap : BlockCapacity (R.comap incl) p)
    (lands : ∀ i : J, ∀ a : Fin (n (j i) + 1), ∃ z, incl z = f ⟨j i,a⟩)
    (wide : ∀ i, 2 ≤ n i) : Nat.card J ≤ p := by
  classical
  let _ := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ↪ I := (Fintype.equivFin J).symm.toEmbedding.trans j
  let n' (i : Fin (Fintype.card J)) := n (e i)
  let back : Vertices n' ↪ Vertices n := Function.Embedding.sigmaMap e (fun _ => Function.Embedding.refl _)
  have adj {a b : Vertices n'} (edge : (forest n').Adj a b) : (forest n).Adj (back a) (back b) := by
    obtain ⟨hne, h | h⟩ := edge
    · exact ⟨fun eq => hne (back.injective eq), Or.inl ⟨congrArg e h.1, h.2⟩⟩
    · exact ⟨fun eq => hne (back.injective eq), Or.inr ⟨congrArg e h.1, h.2⟩⟩
  have pre (a : Vertices n') : ∃ z, incl z = f (back a) :=
    lands ((Fintype.equivFin J).symm a.1) a.2
  let lift (a : Vertices n') : Z := (pre a).choose
  have val (a : Vertices n') : incl (lift a) = f (back a) := (pre a).choose_spec
  have copy : (forest n').IsContained (R.comap incl) := by
    refine ⟨{ toHom := { toFun := lift, map_rel' := ?_ }, injective' := ?_ }⟩
    · intro a b edge
      change R.Adj (incl (lift a)) (incl (lift b))
      rw [val,val]; exact f.toHom.map_adj (adj edge)
    · intro a b same
      exact back.injective (f.injective ((val a).symm.trans ((congrArg incl same).trans (val b))))
  simpa [Nat.card_eq_fintype_card] using localCap _ n' (fun i => wide (e i)) copy

private theorem own_neighbor {I : Type*} (n : I → ℕ) (i : I) (pos : 0 < n i)
    (a : Fin (n i + 1)) : ∃ b : Fin (n i + 1), (forest n).Adj ⟨i,a⟩ ⟨i,b⟩ := by
  by_cases eq : a = 0
  · subst a; exact ⟨(⟨0,pos⟩ : Fin (n i)).succ,starEdge n ⟨i,⟨0,pos⟩⟩⟩
  · obtain ⟨l,rfl⟩ := Fin.exists_succ_eq.mpr eq
    exact ⟨0,(starEdge n ⟨i,l⟩).symm⟩

/-- Stars hitting A charge distinct vertices of A. Every remaining star lies
in a single component of the complement of S and charges its local budget. -/
theorem cut_packing_capacity {X : Type*} [Finite X] (G R : SimpleGraph X) (S A : Set X)
    [Fintype (G.induce Sᶜ).ConnectedComponent] (p : (G.induce Sᶜ).ConnectedComponent → ℕ)
    (hRG : R ≤ G)
    (hit : ∀ ⦃x y⦄, R.Adj x y → x ∈ S → x ∈ A ∨ y ∈ A)
    (localCaps : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      BlockCapacity (R.comap (fun z : c.supp => (z.1 : X))) (p c)) :
    BlockCapacity R (A.ncard + ∑ c, p c) := by
  classical
  intro k n wide copy
  obtain ⟨f⟩ := copy
  let P (i : Fin k) := ∃ a : Fin (n i + 1), f ⟨i,a⟩ ∈ A
  let H := {i : Fin k // P i}
  let U := {i : Fin k // ¬ P i}
  let pick (i : H) : ↥A := ⟨f ⟨i.1,i.2.choose⟩, i.2.choose_spec⟩
  have injPick : Function.Injective pick := by
    intro i j eq
    exact Subtype.ext (congrArg Sigma.fst (f.injective (congrArg Subtype.val eq)))
  have hitCount : Nat.card H ≤ A.ncard := Nat.card_le_card_of_injective pick injPick
  let Y := G.induce Sᶜ
  have outside (i : U) (a : Fin (n i.1 + 1)) : f ⟨i.1,a⟩ ∉ S := by
    intro bad
    obtain ⟨b,edge⟩ := own_neighbor n i.1 (lt_of_lt_of_le (by decide : 0 < 2) (wide i.1)) a
    rcases hit (f.toHom.map_adj edge) bad with ha | hb
    · exact i.2 ⟨a,ha⟩
    · exact i.2 ⟨b,hb⟩
  let pt (i : U) (a : Fin (n i.1 + 1)) : ↥(Sᶜ : Set X) := ⟨f ⟨i.1,a⟩,outside i a⟩
  let label (i : U) : Y.ConnectedComponent := Y.connectedComponentMk (pt i 0)
  have sameLabel (i : U) (a : Fin (n i.1 + 1)) : Y.connectedComponentMk (pt i a) = label i := by
    by_cases ha : a = 0
    · subst a; rfl
    · obtain ⟨l,rfl⟩ := Fin.exists_succ_eq.mpr ha
      apply SimpleGraph.ConnectedComponent.sound
      apply SimpleGraph.Adj.reachable
      exact hRG (f.toHom.map_adj (starEdge n ⟨i.1,l⟩).symm)
  have componentCount (c : Y.ConnectedComponent) : Nat.card {i : U // label i = c} ≤ p c := by
    let j : {i : U // label i = c} ↪ Fin k :=
      { toFun := fun i => i.1.1, inj' := fun _ _ eq => Subtype.ext (Subtype.ext eq) }
    apply subfamily_card_of_block f j (fun z : c.supp => (z.1 : X)) (localCaps c) _ wide
    intro i a
    exact ⟨⟨pt i.1 a,(sameLabel i.1 a).trans i.2⟩,rfl⟩
  have rest : Nat.card U = ∑ c : Y.ConnectedComponent, Nat.card {i : U // label i = c} := by
    rw [← Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv label)).symm
  have byBlocks : Nat.card U ≤ ∑ c, p c := rest ▸ Finset.sum_le_sum (fun c _ => componentCount c)
  have total : Nat.card H + Nat.card U = k := by
    simpa [H,U] using Nat.card_congr (Equiv.sumCompl P)
  omega

#print axioms subfamily_card_of_block
#print axioms cut_packing_capacity
end JSP452Audit.StarHost
