import HallNeighborhoods
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Sum

namespace JSP452Audit.StarHost

/-- A single Hall bijection realizes both nested restrictions on dummy seats.
Components outside F can use all d slots; those in F can use the first k;
those in H can use only the first r. -/
theorem nested_class_hall {R C : Type*} [Finite R] [Finite C]
    (L : R → C → Prop) (H F : Set C) (d k r : ℕ) (nested : H ⊆ F) (rk : r ≤ k) (kd : k ≤ d)
    (balance : Nat.card C = Nat.card R+d)
    (all : ∀ T : Set C, T.ncard ≤ (rootNeighbors L T).ncard+d)
    (full : ∀ T : Set C, T ⊆ F → T.ncard ≤ (rootNeighbors L T).ncard+k)
    (inner : ∀ T : Set C, T ⊆ H → T.ncard ≤ (rootNeighbors L T).ncard+r) :
    ∃ e : C ≃ (R ⊕ Fin d),
      (∀ c a, e c = .inl a → L a c) ∧
      (∀ c i, c∈F → e c = .inr i → i.val<k) ∧
      (∀ c i, c∈H → e c = .inr i → i.val<r) := by
  classical
  let _ := Fintype.ofFinite R
  let _ := Fintype.ofFinite C
  let allows (c : C) (i : ℕ) := (c∈F → i<k) ∧ (c∈H → i<r)
  let legal (c : C) : R ⊕ Fin d → Prop := Sum.elim (fun a => L a c) (fun i => allows c i.val)
  let nbr (c : C) := Finset.univ.filter (legal c)
  have enough_seats (T : Finset C) (c : C) (hc : c∈T) (b : ℕ) (bd : b≤d)
      (available : ∀ i : Fin b, allows c i.val) :
      (rootNeighbors L (T : Set C)).ncard+b ≤ (T.biUnion nbr).card := by
    let N := rootNeighbors L (T : Set C)
    let slot : Fin b ↪ Fin d := Fin.castLEEmb bd
    have left (a : N) : (Sum.inl a.val : R ⊕ Fin d) ∈ T.biUnion nbr := by
      obtain ⟨s,hs,inc⟩ := a.property
      exact Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩⟩
    have right (i : Fin b) : (Sum.inr (slot i) : R ⊕ Fin d) ∈ T.biUnion nbr :=
      Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨Finset.mem_univ _,available i⟩⟩
    let send : N ⊕ Fin b → ↥(T.biUnion nbr) :=
      Sum.elim (fun a => ⟨.inl a.val,left a⟩) (fun i => ⟨.inr (slot i),right i⟩)
    have injects : Function.Injective send := by
      rintro (a|i) (b|j) same
      · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val same)))
      · have bad : (Sum.inl a.val : R ⊕ Fin d) = .inr (slot j) := congrArg Subtype.val same
        cases bad
      · have bad : (Sum.inr (slot i) : R ⊕ Fin d) = .inl b.val := congrArg Subtype.val same
        cases bad
      · exact congrArg Sum.inr (slot.injective (Sum.inr.inj (congrArg Subtype.val same)))
    have bound := Nat.card_le_card_of_injective send injects
    rw [Nat.card_sum,Nat.card_fin,Nat.card_eq_fintype_card (α := ↥(T.biUnion nbr)),Fintype.card_coe] at bound
    exact bound
  have hall (T : Finset C) : T.card ≤ (T.biUnion nbr).card := by
    by_cases nonempty : T.Nonempty
    · by_cases inF : (T : Set C) ⊆ F
      · by_cases inH : (T : Set C) ⊆ H
        · obtain ⟨c,hc⟩ := nonempty
          have bound := inner T inH
          rw [Set.ncard_coe_finset] at bound
          exact bound.trans (enough_seats T c hc r (rk.trans kd)
            (fun i => ⟨fun _ => i.isLt.trans_le rk,fun _ => i.isLt⟩))
        · obtain ⟨c,hc,out⟩ := Set.not_subset.mp inH
          have bound := full T inF
          rw [Set.ncard_coe_finset] at bound
          exact bound.trans (enough_seats T c hc k kd
            (fun i => ⟨fun _ => i.isLt,fun inside => (out inside).elim⟩))
      · obtain ⟨c,hc,out⟩ := Set.not_subset.mp inF
        have bound := all T
        rw [Set.ncard_coe_finset] at bound
        exact bound.trans (enough_seats T c hc d le_rfl
          (fun _ => ⟨fun inside => (out inside).elim,fun inside => (out (nested inside)).elim⟩))
    · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
      simp
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  have bij := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨inj,by simpa only [Nat.card_sum,Nat.card_fin] using balance⟩
  let e := Equiv.ofBijective f bij
  have gets (c : C) : legal c (e c) := (Finset.mem_filter.mp (mem c)).2
  refine ⟨e,?_,?_,?_⟩
  · intro c a eq
    exact (show legal c (.inl a) from eq ▸ gets c)
  · intro c i inside eq
    have ok : allows c i.val := (show legal c (.inr i) from eq ▸ gets c)
    exact ok.1 inside
  · intro c i inside eq
    have ok : allows c i.val := (show legal c (.inr i) from eq ▸ gets c)
    exact ok.2 inside

#print axioms nested_class_hall
end JSP452Audit.StarHost
