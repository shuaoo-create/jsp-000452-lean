import SinglePreferredPositive
import DetachedPairPositiveReserve
import CrossingPositiveReserve

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

private noncomputable def original_part_iso (Q : SimpleGraph X) (I : Set X) (T : Set ↥(Iᶜ : Set X)) :
    ((Q.induce Iᶜ).induce T) ≃g Q.induce (Subtype.val '' T) where
  toFun v := ⟨v.val.val,⟨v.val,v.property,rfl⟩⟩
  invFun v := ⟨v.property.choose,v.property.choose_spec.1⟩
  left_inv v := Subtype.ext (Subtype.ext
    (show (show _ from (⟨v.val.val,⟨v.val,v.property,rfl⟩⟩ : ↥(Subtype.val '' T)).property.choose).val=v.val.val
      from (⟨v.val.val,⟨v.val,v.property,rfl⟩⟩ : ↥(Subtype.val '' T)).property.choose_spec.2))
  right_inv v := Subtype.ext v.property.choose_spec.2
  map_rel_iff' := Iff.rfl

/-- The three branches are tested on one preferred part of the same matching:
crossing, detached with another big part, or a single nontrivial part. -/
theorem no_exception_preferred_positive (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (six : 6≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))) (big : 3≤(mateBlock (Q.induce Iᶜ) N p.val).ncard)
    (conn : ((Q.induce Iᶜ).induce (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N)).Connected)
    (others : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)),j≠p →
      (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val)) :
    1≤baseReserve Q D := by
  classical
  let H := Q.induce Iᶜ
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  let P := mateBlock H N p.val∪zeroMateRegion H N
  by_cases detached : ∀j:J,j≠p → ∀a∈P,∀b∈mateBlock H N j.val,¬H.Adj a b
  · by_cases two : ∃j:J,j≠p ∧ 3≤(mateBlock H N j.val).ncard
    · obtain ⟨q,qp,bq⟩ := two
      exact positive_reserve_of_two_detached_blocks Q I ind largest D six par reg crit N hm max
        gap noEx p q qp big bq others detached
    have single (j:J) (jp:j≠p) : (mateBlock H N j.val).ncard=1 := by
      have little : ¬3≤(mateBlock H N j.val).ncard := fun h => two ⟨j,jp,h⟩
      have odd := Nat.odd_iff.mp (mateBlock_odd H N hm j.val j.property)
      omega
    obtain ⟨s,eq⟩ := actual_single_preferred Q I N hm max gap noEx p big single
    apply single_preferred_positive_reserve Q I ind largest many D six par reg crit s
    · rw [eq]
      exact (original_part_iso Q I P).preconnected_iff.mp conn.preconnected
    · rw [eq]
      have limit (U : Set ↥(Iᶜ : Set X)) (si : H.IsIndepSet U) : U.ncard≤N.vertsᶜ.ncard+1 := by
        have imageInd : Q.IsIndepSet (Subtype.val '' U) := by
          rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne edge
          exact si ha hb (fun e => ne (congrArg Subtype.val e)) edge
        have cap := largest _ imageInd
        rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
      have small := block_with_zero_region_small H N hm max p.val p.property limit
      let e := original_part_iso Q I P
      intro a b c ab ac bc
      have inv {v w : ↥(Subtype.val '' P)} (h : v≠w) : e.symm v≠e.symm w :=
        fun eq => h (e.symm.injective eq)
      rcases small (e.symm a) (e.symm b) (e.symm c) (inv ab) (inv ac) (inv bc) with h|h|h
      · exact Or.inl (e.symm.map_rel_iff.mp h)
      · exact Or.inr (Or.inl (e.symm.map_rel_iff.mp h))
      · exact Or.inr (Or.inr (e.symm.map_rel_iff.mp h))
  push Not at detached
  obtain ⟨q,qp,a,ha,b,hb,edge⟩ := detached
  exact positive_reserve_of_preferred_crossing Q I ind largest D six par reg crit N hm max gap noEx
    p q qp conn.preconnected others ⟨a,ha⟩ ⟨b,hb⟩ edge

/-- Applied to the original unpaid connected regular factor-critical component,
a genuine exceptional region is necessary in the selected decomposition. -/
theorem unpaid_large_component_requires_exception (Q : SimpleGraph X) (D k : ℕ)
    (six : 6≤D) (conn : Q.Connected) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (fail : envelopeReserve Q k<minimumExposure Q D) :
    ∃ (I : Set X) (v : X) (M : Q.Subgraph),
      Q.IsIndepSet I ∧ (∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard) ∧ 3≤I.ncard ∧ v∈I ∧
      M.IsMatching ∧ M.verts={x|x≠v} ∧ M.edgeSet.ncard=matchingEdges Q ∧
      let H := Q.induce Iᶜ
      let N := restrictedOutsideMatching Q I M
      N.IsMatching ∧ N.edgeSet.ncard=matchingEdges H ∧ exceptionalMateRegion H N≠∅ := by
  obtain ⟨I,v,M,ind,largest,three,vi,m,supp,opt,hm,max,_,labels,count,_,anti,_⟩ :=
    unpaid_regular_mate_decomposition Q D k (by omega) reg crit fail
  let H := Q.induce Iᶜ
  let N := restrictedOutsideMatching Q I M
  refine ⟨I,v,M,ind,largest,three,vi,m,supp,opt,hm,max,?_⟩
  intro noEx
  have ord := factorCritical_order_rank Q crit v
  have even := regular_even_on_odd Q D (show Odd (Nat.card X) from ⟨matchingEdges Q,by omega⟩) reg
  have exp := regular_factorCritical_exposure Q crit v D reg
  have env := (envelope_reserve_account Q D).2
  have trunc := envelopeReserve_le_truncation Q D k (fun u => (reg u).le)
  have zero : baseReserve Q D=0 := by omega
  have gap : N.vertsᶜ.ncard+1=I.ncard := by
    rwa [←labels,Set.ncard_image_of_injective _ Subtype.val_injective] at count
  have cl := (pullback_mate_antineighborhood_clique Q I N _ labels anti).subset (zeroMateRegion_subset_anti H N)
  have big := zero_reserve_has_nontrivial_block Q I conn ind largest three D six even reg crit zero N hm max gap noEx cl
  obtain ⟨w,hw,large,joined,others⟩ :=
    exists_preferred_connected_block Q I ind largest D even reg N hm max gap noEx cl big
  have paid := no_exception_preferred_positive Q I ind largest three D six even reg crit N hm max gap noEx
    ⟨w,hw⟩ large joined (fun j ne => others j.val j.property (fun eq => ne (Subtype.ext eq)))
  omega

#print axioms no_exception_preferred_positive
#print axioms unpaid_large_component_requires_exception
end JSP452Audit.StarHost
