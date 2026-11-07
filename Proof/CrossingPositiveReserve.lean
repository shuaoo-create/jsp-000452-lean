import ThreePathDeletionWitness
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V : Type*} [Finite V] [Nonempty V]

/-- The original regular factor-critical component has positive reserve
whenever its connected preferred union has a genuine edge to a companion
clique. The argument builds the deletion and matching at layer D−1. -/
theorem positive_reserve_of_preferred_crossing (Q : SimpleGraph V) (I : Set V)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set V,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
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
  obtain ⟨s,count,_,_⟩ := original_crossing_shape Q I ind largest D six par reg N hm max gap noEx
    p q qp conn others x y edge
  obtain ⟨U,size,wit⟩ := three_path_original_witness Q I ind largest D six par reg s count
  have cut := deletionBudget_le_of_witness Q (D-1) U wit
  by_contra! fail
  have zero : baseReserve Q D=0 := by omega
  have present := (Set.ncard_pos (Set.toFinite I)).mp (show 0<I.ncard by omega)
  obtain ⟨_,equal⟩ := (zero_reserve_independent_cut Q D (by omega) reg crit zero I present ind).2.2
    (D-1) (by omega) (by omega)
  omega

#print axioms positive_reserve_of_preferred_crossing
end JSP452Audit.StarHost
