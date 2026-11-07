import EqualIndependentSides
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Remove the exceptional vertex and all but two of its singleton
neighbours. The whole old independent root set survives this deletion. -/
theorem equal_sides_deletion_witness (Q : SimpleGraph X) (I Y : Set X) (a : X)
    (D : ℕ) (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (ind : Q.IsIndepSet I) (other : Q.IsIndepSet Y) (dis : Disjoint I Y)
    (ai : a∉I) (ay : a∉Y) (cover : ∀v,v∈I ∨ v∈Y ∨ v=a) (size : Y.ncard=I.ncard) :
    ∃U:Set X,U.ncard+1=I.ncard ∧ admits_matching_remainder (Q.induce Uᶜ) (D-1) := by
  classical
  have degree := (equal_sides_pivot_degrees Q I Y a D reg ind other dis ai ay cover size).2
  obtain ⟨u,v,⟨au,uy⟩,⟨av,vy⟩,uv⟩ := (Set.one_lt_ncard_iff (Set.toFinite (Q.neighborSet a∩Y))).mp (by omega)
  let S := Y\{u,v}
  let U := insert a S
  have au' : a∈U := Set.mem_insert _ _
  have paid : U.ncard+1=I.ncard := by
    have inc : ({u,v} : Set X)⊆Y := Set.insert_subset uy (Set.singleton_subset_iff.mpr vy)
    have diff := Set.ncard_sdiff_add_ncard_of_subset inc
    rw [Set.ncard_pair uv] at diff
    change S.ncard+2=Y.ncard at diff
    rw [show U=insert a S from rfl,Set.ncard_insert_of_notMem (show a∉S from fun h => ay h.1)]
    omega
  let K := Q.induce Uᶜ
  let L : Set ↥(Uᶜ : Set X) := {w | w.val∈I}
  have remainder (w : ↥(Uᶜ : Set X)) : w.val∈I ∨ w.val=u ∨ w.val=v := by
    rcases cover w.val with i|y|e
    · exact Or.inl i
    · by_cases wu : w.val=u
      · exact Or.inr (Or.inl wu)
      by_cases wv : w.val=v
      · exact Or.inr (Or.inr wv)
      exact (w.property (Or.inr ⟨y,by simp [wu,wv]⟩)).elim
    · exact (w.property (Or.inl e)).elim
  have root (w:↥(Uᶜ : Set X)) (wi:w.val∈I) : Nat.card (K.neighborSet w)≤2 := by
    have sub : Q.neighborSet w.val∩Uᶜ⊆{u,v} := by
      rintro z ⟨edge,hz⟩
      rcases remainder ⟨z,hz⟩ with zi|e|e
      · exact (ind wi zi (show Q.Adj w.val z from edge).ne edge).elim
      · exact Or.inl e
      · exact Or.inr (Set.mem_singleton_iff.mpr e)
    rw [show K=Q.induce Uᶜ from rfl,induced_degree_intersection]
    exact (Set.ncard_le_ncard sub).trans (Set.ncard_pair uv).le
  have drop (w:↥(Uᶜ : Set X)) (edge:Q.Adj a w.val) : Nat.card (K.neighborSet w)≤D-1 := by
    have strict : Q.neighborSet w.val∩Uᶜ ⊂ Q.neighborSet w.val :=
      ⟨Set.inter_subset_left,fun back => (back edge.symm).2 au'⟩
    have h := Set.ncard_lt_ncard strict
    rw [←Nat.card_coe_set_eq (Q.neighborSet w.val),reg] at h
    rw [show K=Q.induce Uᶜ from rfl,induced_degree_intersection];omega
  refine ⟨U,paid,remainder_via_bipartite_cut K L (D-1) (by omega) ?_ ?_⟩
  · intro w
    rcases remainder w with h|e|e
    · have b := root w h;omega
    · exact drop w (show Q.Adj a w.val from e.symm ▸ au)
    · exact drop w (show Q.Adj a w.val from e.symm ▸ av)
  · intro w full z edge
    have wz : Q.Adj w.val z.val := edge
    rcases remainder w with h|e|e
    · exact iff_of_true h (fun zi => ind h zi wz.ne wz)
    · have wy : w.val∈Y := e.symm ▸ uy
      have zi : z.val∈I := by
        rcases remainder z with h|e|e
        · exact h
        · exact (other wy (e.symm ▸ uy) wz.ne wz).elim
        · exact (other wy (e.symm ▸ vy) wz.ne wz).elim
      exact iff_of_false (fun wi => Set.disjoint_left.mp dis wi wy) (fun h => h zi)
    · have wy : w.val∈Y := e.symm ▸ vy
      have zi : z.val∈I := by
        rcases remainder z with h|e|e
        · exact h
        · exact (other wy (e.symm ▸ uy) wz.ne wz).elim
        · exact (other wy (e.symm ▸ vy) wz.ne wz).elim
      exact iff_of_false (fun wi => Set.disjoint_left.mp dis wi wy) (fun h => h zi)

theorem exceptional_singletons_positive [Nonempty X] (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (D : ℕ) (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) {J:Type*} [Fintype J]
    (a : ↥(Iᶜ : Set X)) (F : J→Set ↥(Iᶜ : Set X)) (count : Fintype.card J=I.ncard)
    (dis : ∀i j,i≠j → Disjoint (F i) (F j)) (off : ∀i,a∉F i)
    (cover : ∀v,v≠a → ∃i,v∈F i) (sep : ∀i j,i≠j → ∀v∈F i,∀w∈F j,¬(Q.induce Iᶜ).Adj v w)
    (ones : ∀i,(F i).ncard=1) : 1≤baseReserve Q D := by
  obtain ⟨Y,yi,iy,ay,card,cov⟩ := all_singleton_original_sides Q I a F count dis off cover sep ones
  obtain ⟨U,paid,witness⟩ := equal_sides_deletion_witness Q I Y a.val D four reg ind yi iy a.property ay cov card
  have bound := deletionBudget_le_of_witness Q (D-1) U witness
  by_contra! fail
  have zero : baseReserve Q D=0 := by omega
  have present := (Set.ncard_pos (Set.toFinite I)).mp (show 0<I.ncard by omega)
  have eq := ((zero_reserve_independent_cut Q D (by omega) reg crit zero I present ind).2.2
    (D-1) (by omega) (by omega)).2
  omega

#print axioms equal_sides_deletion_witness
#print axioms exceptional_singletons_positive
end JSP452Audit.StarHost
