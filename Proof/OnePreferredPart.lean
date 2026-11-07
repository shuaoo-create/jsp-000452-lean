import DetachedPairPositiveReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

structure OnePreferredPart {X : Type*} (Q : SimpleGraph X) (I : Set X) where
  preferred : Set X
  singles : Set X
  pOut : preferred⊆Iᶜ
  sOut : singles⊆Iᶜ
  dis : Disjoint singles preferred
  cover : ∀v,v∈I ∨ v∈singles ∨ v∈preferred
  isolated : ∀s∈singles,∀v,Q.Adj s v → v∈I
  external : ∀a∈preferred,∀v,Q.Adj a v → v∉preferred → v∈I
  count : singles.ncard+2=I.ncard
  odd : Odd preferred.ncard
  big : 3≤preferred.ncard

/-- Restore the one-block branch on original labels; every other hole is
isolated in the residual graph. -/
theorem actual_single_preferred (Q : SimpleGraph X) (I : Set X) (N : (Q.induce Iᶜ).Subgraph)
    (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)))
    (big : 3≤(mateBlock (Q.induce Iᶜ) N p.val).ncard)
    (single : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)),j≠p →
      (mateBlock (Q.induce Iᶜ) N j.val).ncard=1) :
    ∃ f : OnePreferredPart Q I,
      f.preferred=Subtype.val '' (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N) := by
  classical
  let H := Q.induce Iᶜ
  let B := mateBlock H N p.val∪zeroMateRegion H N
  let S := N.vertsᶜ\{p.val}
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  have apart : Disjoint S B := by
    apply Set.disjoint_left.mpr
    intro v hv hp
    rcases hp with h|⟨_,e,_,_⟩
    · exact Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N p.val) h hv
    · exact hv.1 (N.edge_vert e)
  have sole {j:J} (jp:j≠p) {v} (hv:v∈mateBlock H N j.val) : v=j.val :=
    (Set.ncard_le_one (Set.toFinite _)).mp (single j jp).le v hv j.val (mateBlock_self H N j.val)
  have union (v : ↥(Iᶜ : Set X)) : v∈S ∨ v∈B := by
    rcases mate_classes_cover H N hm v with ⟨u,hu,hv⟩|hz|ex
    · let j : J := ⟨u,hu⟩
      by_cases jp:j=p
      · exact Or.inr (Or.inl (jp ▸ (hv : v∈mateBlock H N j.val)))
      have eq := sole jp hv
      have us : j.val∈S := ⟨hu,fun h => jp (Subtype.ext (Set.mem_singleton_iff.mp h))⟩
      exact Or.inl (eq.symm ▸ us)
    · exact Or.inr (Or.inr hz)
    · exact (noEx ▸ ex : v∈(∅ : Set ↥(Iᶜ : Set X))).elim
  have iso (s) (hs:s∈S) (v) : ¬H.Adj s v := by
    rcases mate_classes_cover H N hm v with ⟨u,hu,hv⟩|⟨_,_,av,_⟩|ex
    · by_cases eq : s=u
      · let j : J := ⟨s,hs.1⟩
        have own : v=j.val := sole (fun h => hs.2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val h)))
          (show v∈mateBlock H N s from eq.symm ▸ hv)
        exact fun e => e.ne own.symm
      · exact fun e => mateBlock_separated H N hm max hu v hv s ⟨hs.1,by simpa using eq⟩ e.symm
    · exact fun e => av s hs.1 e.symm
    · exact (noEx ▸ ex : v∈(∅ : Set ↥(Iᶜ : Set X))).elim
  have out (T : Set ↥(Iᶜ : Set X)) : Subtype.val '' T⊆Iᶜ := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have pCard := Set.ncard_image_of_injective B Subtype.val_injective
  have sCard := Set.ncard_image_of_injective S Subtype.val_injective
  refine ⟨{
    preferred := Subtype.val '' B
    singles := Subtype.val '' S
    pOut := out _
    sOut := out _
    dis := Set.disjoint_image_of_injective Subtype.val_injective apart
    cover := ?_
    isolated := ?_
    external := ?_
    count := ?_
    odd := pCard.symm ▸ preferred_region_odd H N hm p.val p.property
    big := pCard.symm ▸ big.trans (Set.ncard_le_ncard Set.subset_union_left)
  },rfl⟩
  · intro v
    by_cases vi : v∈I
    · exact Or.inl vi
    let w : ↥(Iᶜ : Set X) := ⟨v,vi⟩
    exact (union w).elim (fun h => Or.inr (Or.inl ⟨w,h,rfl⟩)) (fun h => Or.inr (Or.inr ⟨w,h,rfl⟩))
  · rintro _ ⟨s,hs,rfl⟩ v edge
    by_contra vi
    exact iso s hs ⟨v,vi⟩ edge
  · rintro _ ⟨a,ha,rfl⟩ v edge outside
    by_contra vi
    let w : ↥(Iᶜ : Set X) := ⟨v,vi⟩
    rcases union w with hs|hb
    · exact iso w hs a edge.symm
    · exact outside ⟨w,hb,rfl⟩
  · rw [sCard]
    have minus := Set.ncard_sdiff_singleton_add_one p.property
    change (N.vertsᶜ\{p.val}).ncard+2=I.ncard
    omega

/-- In the detached one-block case, all roots send exactly 2D edges to the
preferred part once the D edges at every singleton have been accounted for. -/
theorem one_preferred_exact_boundary (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (D : ℕ) (reg : ∀v,Nat.card (Q.neighborSet v)=D) (s : OnePreferredPart Q I) :
    crossCount Q s.preferred s.preferredᶜ=2*D ∧ crossCount Q I s.preferred=2*D := by
  classical
  let _ := Fintype.ofFinite I
  let S := s.singles
  let P := s.preferred
  have outside : S∪P=Iᶜ := by
    ext v
    constructor
    · exact fun h => h.elim (fun hs => s.sOut hs) (fun hp => s.pOut hp)
    · intro h
      exact (s.cover v).elim (fun hi => (h hi).elim) id
  have total : crossCount Q I Iᶜ=I.ncard*D := by
    rw [crossCount_eq_neighbor_sum]
    calc
      _ = ∑ _ : I,D := Finset.sum_congr rfl (fun v _ => by
        have sub : Q.neighborSet v.val⊆Iᶜ := fun w adj hw => ind v.property hw (show Q.Adj v.val w from adj).ne adj
        rw [Set.inter_eq_left.mpr sub,←Nat.card_coe_set_eq,reg])
      _ = _ := by simp [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have add : crossCount Q I Iᶜ=crossCount Q I S+crossCount Q I P := by
    rw [crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [←outside,Set.inter_union_distrib_left,Set.ncard_union_eq
      (s.dis.mono Set.inter_subset_right Set.inter_subset_right)]
  have costS : crossCount Q I S=S.ncard*D := uniform_cross_count Q S I D (by
    intro v hv
    have sub := s.isolated v hv
    rw [Set.inter_eq_left.mpr (show Q.neighborSet v⊆I from sub),←Nat.card_coe_set_eq,reg])
  have transfer : crossCount Q P Pᶜ=crossCount Q I P := by
    let _ := Fintype.ofFinite P
    rw [crossCount_swap Q I P,crossCount_eq_neighbor_sum,crossCount_eq_neighbor_sum]
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    ext b
    exact ⟨fun h => ⟨h.1,s.external v.val v.property b h.1 h.2⟩,fun h => ⟨h.1,fun bp => s.pOut bp h.2⟩⟩
  rw [total,costS,←s.count,Nat.add_mul] at add
  change S.ncard*D+2*D=S.ncard*D+crossCount Q I P at add
  have pay := Nat.add_left_cancel add
  exact ⟨transfer.trans pay.symm,pay.symm⟩

#print axioms actual_single_preferred
#print axioms one_preferred_exact_boundary
end JSP452Audit.StarHost
