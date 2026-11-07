import CrossingLabelsFromFour
import ExceptionalPartitionPays
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V : Type*} [Finite V]

/-- The two leaves of the preferred path become two genuine singleton
neighbours when its middle vertex is included with the roots. -/
theorem path_as_heavy_clique_frame (Q : SimpleGraph V) (I : Set V) (D : ℕ)
    (s : ThreePathShape (Q.induce Iᶜ) D) (count : s.singles.ncard+3=I.ncard) :
    ∃h : HeavyCliqueFrame Q I D,h.pivot=s.pivot.val ∧ h.cliquePart=Subtype.val '' s.companion := by
  classical
  let H := Q.induce Iᶜ
  let T := insert s.left (insert s.right s.singles)
  have lf := s.path_free s.left (by simp)
  have rf := s.path_free s.right (by simp)
  have pf := s.path_free s.pivot (by simp)
  have ts : T.ncard=s.singles.ncard+2 := by
    change (insert s.left (insert s.right s.singles)).ncard=s.singles.ncard+2
    rw [Set.ncard_insert_of_notMem (by simp [s.different,lf.1]),Set.ncard_insert_of_notMem rf.1]
  have dis : Disjoint T s.companion := by
    apply Set.disjoint_left.mpr
    rintro v (h|h|h) hc
    · exact lf.2 (h ▸ hc)
    · exact rf.2 (h ▸ hc)
    · exact Set.disjoint_left.mp s.clean h hc
  have outside (A : Set ↥(Iᶜ : Set V)) : Subtype.val '' A⊆Iᶜ := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have pivotFree : s.pivot∉T := by simp [T,Ne.symm s.left_off,Ne.symm s.right_off,pf.1]
  have exitT (v) (hv:v∈T) (w) (adj:H.Adj v w) : w=s.pivot := by
    rcases hv with eq|eq|hs
    · have mem : w∈H.neighborSet s.left := eq ▸ adj
      rw [show H.neighborSet s.left={s.pivot} from s.left_neighbors] at mem
      exact Set.mem_singleton_iff.mp mem
    · have mem : w∈H.neighborSet s.right := eq ▸ adj
      rw [show H.neighborSet s.right={s.pivot} from s.right_neighbors] at mem
      exact Set.mem_singleton_iff.mp mem
    · exact (s.isolated v hs w adj).elim
  have lx : H.Adj s.pivot s.left := (show H.Adj s.left s.pivot from
    (show s.pivot∈H.neighborSet s.left by rw [s.left_neighbors];simp)).symm
  have rx : H.Adj s.pivot s.right := (show H.Adj s.right s.pivot from
    (show s.pivot∈H.neighborSet s.right by rw [s.right_neighbors];simp)).symm
  refine ⟨{
    pivot := s.pivot.val
    singles := Subtype.val '' T
    cliquePart := Subtype.val '' s.companion
    ai := s.pivot.property
    sOut := outside _
    cOut := outside _
    dis := Set.disjoint_image_of_injective Subtype.val_injective dis
    as_ := ?_
    ac := ?_
    cover := ?_
    singleEdges := ?_
    cliqueEdges := ?_
    clique := ?_
    order := (Set.ncard_image_of_injective _ Subtype.val_injective).trans s.clique_order
    count := ?_
    two := ⟨s.left.val,⟨s.left,Or.inl rfl,rfl⟩,s.right.val,⟨s.right,Or.inr (Or.inl rfl),rfl⟩,
      fun eq => s.different (Subtype.ext eq),lx,rx⟩
  },rfl,rfl⟩
  · rintro ⟨v,ht,eq⟩;exact pivotFree ((Subtype.ext eq : v=s.pivot) ▸ ht)
  · rintro ⟨v,hc,eq⟩;exact pf.2 ((Subtype.ext eq : v=s.pivot) ▸ hc)
  · intro v
    by_cases vi:v∈I
    · exact Or.inl vi
    let w : ↥(Iᶜ : Set V) := ⟨v,vi⟩
    rcases s.cover w with h|h|h|h|h
    · exact Or.inr (Or.inr (Or.inl ⟨w,Or.inr (Or.inr h),rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨w,h,rfl⟩))
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl ⟨w,Or.inl h,rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨w,Or.inr (Or.inl h),rfl⟩))
  · rintro _ ⟨v,hv,rfl⟩ w adj
    by_cases wi:w∈I
    · exact Or.inl wi
    · exact Or.inr (congrArg Subtype.val (exitT v hv ⟨w,wi⟩ adj))
  · rintro _ ⟨v,hv,rfl⟩ w adj out
    by_cases wi:w∈I
    · exact Or.inl wi
    let u : ↥(Iᶜ : Set V) := ⟨w,wi⟩
    rcases s.cover u with hs|hc|same|same|same
    · exact (s.isolated u hs v adj.symm).elim
    · exact (out ⟨u,hc,rfl⟩).elim
    · exact Or.inr (congrArg Subtype.val same)
    · exact (pf.2 ((exitT u (Or.inl same) v adj.symm) ▸ hv)).elim
    · exact (pf.2 ((exitT u (Or.inr (Or.inl same)) v adj.symm) ▸ hv)).elim
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne
    exact s.clique hv hw (fun eq => ne (congrArg Subtype.val eq))
  · rw [Set.ncard_image_of_injective _ Subtype.val_injective,ts];omega

variable [Nonempty V]

theorem crossing_positive_from_four (Q : SimpleGraph V) (I : Set V)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set V,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p q : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V))) (qp : q≠p)
    (conn : ((Q.induce Iᶜ).induce (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N)).Preconnected)
    (others : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V)), j≠p → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val))
    (x : ↥(mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N))
    (y : mateBlock (Q.induce Iᶜ) N q.val) (edge : (Q.induce Iᶜ).Adj x.val y.val) :
    1≤baseReserve Q D := by
  obtain ⟨s,count,_,_⟩ := original_crossing_shape_from_four Q I ind largest D four par reg N hm max
    gap noEx p q qp conn others x y edge
  obtain ⟨h,_,_⟩ := path_as_heavy_clique_frame Q I D s count
  exact exceptional_large_clique_positive Q I ind largest D four par reg crit h

#print axioms path_as_heavy_clique_frame
#print axioms crossing_positive_from_four
end JSP452Audit.StarHost
