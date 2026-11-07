import SmallAlphaPerfect

namespace JSP452Audit.StarHost
open SimpleGraph

/-- After removal of three labels, a cut without Q-edges would force both
sides to use every complementary degree across the cut. The three removed
vertices would then form a complementary triangle, violating the hypothesis. -/
theorem triple_deleted_preconnected {X : Type*} [Finite X] (Q : SimpleGraph X) (c : ℕ)
    (regular : ∀ x, Nat.card (Qᶜ.neighborSet x) = c) (two : 2≤c)
    (size : 2*c+3 ≤ Nat.card X) (small : NoIndependentTriple Q)
    (S : Set X) (three : S.ncard=3) : (Q.induce Sᶜ).Preconnected := by
  classical
  intro x y
  let H := Q.induce Sᶜ
  change H.Reachable x y
  by_contra apart
  let A : Set X := {z | ∃ hz : z∈Sᶜ, H.Reachable x ⟨z,hz⟩}
  let B := Sᶜ \ A
  have subA : A ⊆ Sᶜ := fun _ h => h.choose
  have subB : B ⊆ Sᶜ := fun _ h => h.1
  have hx : x.val ∈ A := ⟨x.property,Reachable.refl _⟩
  have hy : y.val ∈ B := ⟨y.property,fun h => apart h.choose_spec⟩
  have cross {a b : X} (ha : a∈A) (hb : b∈B) : Qᶜ.Adj a b := by
    apply (Q.compl_adj _ _).mpr
    refine ⟨fun eq => hb.2 (eq ▸ ha),?_⟩
    intro edge
    obtain ⟨haS,reach⟩ := ha
    exact hb.2 ⟨hb.1,reach.trans (show H.Adj ⟨a,haS⟩ ⟨b,hb.1⟩ from edge).reachable⟩
  have intoB {a : X} (ha : a∈A) : B ⊆ Qᶜ.neighborSet a := fun _ hb => cross ha hb
  have intoA {b : X} (hb : b∈B) : A ⊆ Qᶜ.neighborSet b := fun _ ha => (cross ha hb).symm
  have sizeA := (Set.ncard_le_ncard (intoA hy)).trans_eq (regular y.val)
  have sizeB := (Set.ncard_le_ncard (intoB hx)).trans_eq (regular x.val)
  have sides : B.ncard+A.ncard=Sᶜ.ncard := Set.ncard_sdiff_add_ncard_of_subset subA
  have all := Set.ncard_add_ncard_compl S
  have exactA : A.ncard=c := by omega
  have exactB : B.ncard=c := by omega
  have sealed {s : X} (hs : s∈S) : Qᶜ.neighborSet s ⊆ S \ {s} := by
    intro t ht
    have edge : Qᶜ.Adj s t := ht
    refine ⟨?_,fun eq => edge.ne (Set.mem_singleton_iff.mp eq).symm⟩
    by_contra outside
    by_cases ha : t∈A
    · have eq := Set.eq_of_subset_of_ncard_le (intoB ha) (by rw [← Nat.card_coe_set_eq,regular,exactB])
      have used : s∈B := eq.symm ▸ (show s∈Qᶜ.neighborSet t from edge.symm)
      exact subB used hs
    · have eq := Set.eq_of_subset_of_ncard_le (intoA (show t∈B from ⟨outside,ha⟩))
        (by rw [← Nat.card_coe_set_eq,regular,exactA])
      have used : s∈A := eq.symm ▸ (show s∈Qᶜ.neighborSet t from edge.symm)
      exact subA used hs
  have triangle {s t : X} (hs : s∈S) (ht : t∈S) (ne : s≠t) : ¬ Q.Adj s t := by
    have cap : (S \ {s}).ncard=2 := by
      rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hs),three,Set.ncard_singleton]
    have eq := Set.eq_of_subset_of_ncard_le (sealed hs) (by rw [cap,←Nat.card_coe_set_eq,regular]; exact two)
    have edge : Qᶜ.Adj s t := (show t∈Qᶜ.neighborSet s by
      rw [eq]
      exact ⟨ht,fun same => ne (Set.mem_singleton_iff.mp same).symm⟩)
    exact ((Q.compl_adj _ _).mp edge).2
  obtain ⟨a,b,d,ab,ad,bd,labels⟩ := Set.ncard_eq_three.mp three
  have ma : a∈S := by rw [labels]; simp
  have mb : b∈S := by rw [labels]; simp
  have md : d∈S := by rw [labels]; simp
  exact (small a b d ab ad bd).elim (triangle ma mb ab)
    (fun h => h.elim (triangle ma md ad) (triangle mb md bd))

#print axioms triple_deleted_preconnected
end JSP452Audit.StarHost
