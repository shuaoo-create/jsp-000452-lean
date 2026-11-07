import SinglePositiveFromFour
import DetachedPairFromFour
import FourCrossingReserve
import UnifiedNoException

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

/-- For the same genuine residual matching, a nonpositive reserve leaves an actual
pair of detached odd parts, including the selected connected preferred region. -/
theorem reserve_or_two_detached_parts_from_four (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (four : 4≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))) (big : 3≤(mateBlock (Q.induce Iᶜ) N p.val).ncard)
    (conn : ((Q.induce Iᶜ).induce (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N)).Connected)
    (others : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)),j≠p →
      (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val)) :
    1≤baseReserve Q D ∨ ∃ (q : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))) (s : DetachedMatePair (Q.induce Iᶜ)),
      q≠p ∧ s.preferred=mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N ∧
      s.companion=mateBlock (Q.induce Iᶜ) N q.val ∧ s.singles.ncard+3=I.ncard := by
  classical
  let H := Q.induce Iᶜ
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  let P := mateBlock H N p.val∪zeroMateRegion H N
  by_cases detached : ∀j:J,j≠p → ∀a∈P,∀b∈mateBlock H N j.val,¬H.Adj a b
  · by_cases two : ∃j:J,j≠p ∧ 3≤(mateBlock H N j.val).ncard
    · obtain ⟨q,qp,bq⟩ := two
      obtain ⟨s,part,comp,count⟩ := actual_detached_pair_from_four Q I ind largest D four par reg N hm max
        gap noEx p q qp big bq others detached
      exact Or.inr ⟨q,s,qp,part,comp,count⟩
    have single (j:J) (jp:j≠p) : (mateBlock H N j.val).ncard=1 := by
      have little : ¬3≤(mateBlock H N j.val).ncard := fun h => two ⟨j,jp,h⟩
      have odd := Nat.odd_iff.mp (mateBlock_odd H N hm j.val j.property)
      omega
    obtain ⟨s,eq⟩ := actual_single_preferred Q I N hm max gap noEx p big single
    left
    apply single_preferred_positive_reserve_from_four Q I ind largest many D four par reg crit s
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
  left
  exact crossing_positive_from_four Q I ind largest D four par reg crit N hm max gap noEx
    p q qp conn.preconnected others ⟨a,ha⟩ ⟨b,hb⟩ edge

#print axioms reserve_or_two_detached_parts_from_four
end JSP452Audit.StarHost
