import OriginalExceptionalPartition
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem cross_union_disjoint (Q : SimpleGraph X) (A U V : Set X) (dis : Disjoint U V) :
    crossCount Q A (U∪V)=crossCount Q A U+crossCount Q A V := by
  classical
  let _ := Fintype.ofFinite A
  rw [crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [Set.inter_union_distrib_left,Set.ncard_union_eq (dis.mono Set.inter_subset_right Set.inter_subset_right)]

theorem cross_to_point (Q : SimpleGraph X) (I : Set X) (a:X) :
    crossCount Q I {a}=(Q.neighborSet a∩I).ncard := by
  have h := uniform_cross_count Q {a} I (Q.neighborSet a∩I).ncard (by rintro v hv;rw [Set.mem_singleton_iff.mp hv])
  simpa using h

/-- For equal independent sides with just one additional vertex, regularity
makes that vertex split its degree equally between them. -/
theorem equal_sides_pivot_degrees (Q : SimpleGraph X) (I Y : Set X) (a:X) (D : ℕ)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (ii : Q.IsIndepSet I) (yi : Q.IsIndepSet Y)
    (dis : Disjoint I Y) (ai : a∉I) (ay : a∉Y)
    (cover : ∀v,v∈I ∨ v∈Y ∨ v=a) (size : Y.ncard=I.ncard) :
    2*(Q.neighborSet a∩I).ncard=D ∧ 2*(Q.neighborSet a∩Y).ncard=D := by
  classical
  have side (S T : Set X) (ind : Q.IsIndepSet S) (at_ : a∉T)
      (cov : ∀v,v∈S ∨ v∈T ∨ v=a) :
      crossCount Q S T+(Q.neighborSet a∩S).ncard=S.ncard*D := by
    have incident (x:X) (hx:x∈S) : Q.neighborSet x⊆T∪{a} := by
      intro v edge
      rcases cov v with h|h|h
      · exact (ind hx h (show Q.Adj x v from edge).ne edge).elim
      · exact Or.inl h
      · exact Or.inr (Set.mem_singleton_iff.mpr h)
    have val := uniform_cross_count Q S (T∪{a}) D (fun x hx => by
      rw [Set.inter_eq_left.mpr (incident x hx),←Nat.card_coe_set_eq,reg])
    rw [crossCount_swap,cross_union_disjoint Q S T {a} (Set.disjoint_singleton_right.mpr at_),cross_to_point] at val
    exact val
  have l := side I Y ii ay cover
  have r := side Y I yi ai (fun v => by rcases cover v with h|h|h <;> tauto)
  rw [crossCount_swap Q Y I,size] at r
  let N := Q.neighborSet a
  have split : (N∩I)∪(N∩Y)=N := by
    ext v
    constructor
    · exact fun h => h.elim (fun k => k.1) (fun k => k.1)
    · intro h
      rcases cover v with k|k|k
      · exact Or.inl ⟨h,k⟩
      · exact Or.inr ⟨h,k⟩
      · exact False.elim ((show Q.Adj a v from h).ne k.symm)
  have sum := congrArg Set.ncard split
  rw [Set.ncard_union_eq (dis.mono Set.inter_subset_right Set.inter_subset_right),
    ←Nat.card_coe_set_eq N,reg] at sum
  change (Q.neighborSet a∩I).ncard+(Q.neighborSet a∩Y).ncard=D at sum
  omega

/-- If every part of the real exceptional partition is a singleton, removing
the heavy endpoint yields a second independent side of exactly |I| labels. -/
theorem all_singleton_original_sides {J : Type*} [Fintype J] (Q : SimpleGraph X) (I : Set X)
    (a : ↥(Iᶜ : Set X)) (F : J→Set ↥(Iᶜ : Set X)) (count : Fintype.card J=I.ncard)
    (dis : ∀i j,i≠j → Disjoint (F i) (F j)) (off : ∀i,a∉F i)
    (cover : ∀v,v≠a → ∃i,v∈F i) (sep : ∀i j,i≠j → ∀v∈F i,∀w∈F j,¬(Q.induce Iᶜ).Adj v w)
    (ones : ∀i,(F i).ncard=1) :
    ∃Y : Set X,Q.IsIndepSet Y ∧ Disjoint I Y ∧ a.val∉Y ∧ Y.ncard=I.ncard ∧
      ∀v,v∈I ∨ v∈Y ∨ v=a.val := by
  classical
  let U := {v : ↥(Iᶜ : Set X) | v≠a}
  let Y := Subtype.val '' U
  have union : (⋃i,F i)=U := by
    ext v
    constructor
    · intro h;obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact fun eq => off i (eq ▸ hi)
    · intro h;exact Set.mem_iUnion.mpr (cover v h)
  have cnt : Y.ncard=I.ncard := by
    rw [show Y.ncard=U.ncard from Set.ncard_image_of_injective _ Subtype.val_injective,←union,
      Set.ncard_iUnion_of_finite (fun i => Set.toFinite (F i)) dis,finsum_eq_sum_of_fintype]
    simpa [ones] using count
  refine ⟨Y,?_,?_,?_,cnt,?_⟩
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ diff edge
    obtain ⟨i,hi⟩ := cover v hv
    obtain ⟨j,hj⟩ := cover w hw
    by_cases eq:i=j
    · exact diff (congrArg Subtype.val ((Set.ncard_le_one (Set.toFinite _)).mp (ones j).le v (eq ▸ hi) w hj))
    · exact sep i j eq v hi w hj edge
  · exact Set.disjoint_left.mpr (by rintro _ h ⟨v,_,rfl⟩;exact v.property h)
  · rintro ⟨v,hv,eq⟩;exact hv (Subtype.ext eq)
  · intro v
    by_cases vi : v∈I
    · exact Or.inl vi
    by_cases va : v=a.val
    · exact Or.inr (Or.inr va)
    · exact Or.inr (Or.inl ⟨⟨v,vi⟩,fun eq => va (congrArg Subtype.val eq),rfl⟩)

#print axioms equal_sides_pivot_degrees
#print axioms all_singleton_original_sides
end JSP452Audit.StarHost
