import IndependentMateBarrier
import MateAntineighborhood
import LargestIndependentLabels
import DominatingPairReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- Every remaining unpaid regular critical host has an actual maximum
independent-set mate decomposition. All sets and both matchings retain the
original graph labels; no dominating pair or model classification is assumed. -/
theorem unpaid_regular_mate_decomposition (Q : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (unpaid : envelopeReserve Q k<minimumExposure Q D) :
    ∃ (I : Set X) (v : X) (M : Q.Subgraph),
      Q.IsIndepSet I ∧ (∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard) ∧
      3≤I.ncard ∧ v∈I ∧ M.IsMatching ∧ M.verts={x|x≠v} ∧ M.edgeSet.ncard=matchingEdges Q ∧
      let N := restrictedOutsideMatching Q I M
      let W := independentMateLabels Q I v M
      N.IsMatching ∧ N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ) ∧
      (∀a b : ↥(Iᶜ : Set X),N.Adj a b ↔ M.Adj a.val b.val) ∧
      Subtype.val '' N.vertsᶜ=W ∧ W.ncard+1=I.ncard ∧ Q.IsIndepSet W ∧
      Q.IsClique (mateAntineighborhood Q W) ∧
      Q.IsClique {x | x∉I ∧ x∉W ∧ ∀w∈W,¬Q.Adj x w} := by
  obtain ⟨triple,_⟩ := unpaid_regular_structure Q D k large reg crit unpaid
  obtain ⟨I,ind,max,three⟩ := largest_independent_set_has_triple_size Q triple
  obtain ⟨v,vi⟩ := Set.nonempty_of_ncard_ne_zero (show I.ncard≠0 by omega)
  obtain ⟨P,hP⟩ := crit v
  obtain ⟨M,hm,expose,maximum⟩ := lift_perfect_off_vertex_maximum Q v P hP
  have exposure := regular_factorCritical_exposure Q crit v D reg
  have account := (envelope_reserve_account Q D).2
  have stable := envelopeReserve_le_truncation Q D k (fun x => (reg x).le)
  have zero : baseReserve Q D=0 := by omega
  obtain ⟨hn,rank,labels,count,indW⟩ := independent_mate_barrier Q D (by omega) reg crit zero I ind v vi M hm expose
  refine ⟨I,v,M,ind,max,three,vi,hm,expose,maximum,hn,rank,?_,labels,count,indW,?_,?_⟩
  · intro a b
    rfl
  · exact mate_antineighborhood_clique Q I _ ind max indW count
  · exact mate_antineighborhood_excluding_I_clique Q I _ ind max indW count

#print axioms unpaid_regular_mate_decomposition
end JSP452Audit.StarHost
