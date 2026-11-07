import NoDisjointRootPair
import ExceptionalSingletonPayment
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- If a connected large-degree original component still failed its reserve
bound, the real exceptional partition would have its unique large clique. -/
theorem unpaid_requires_large_exceptional_clique (Q : SimpleGraph X) (D k : ℕ)
    (six : 6≤D) (conn : Q.Connected) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (fail : envelopeReserve Q k<minimumExposure Q D) :
    ∃I:Set X,Q.IsIndepSet I ∧ (∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard) ∧ 3≤I.ncard ∧
      ∃s : HeavyCliqueFrame Q I D, ∃ (v : X) (M : Q.Subgraph),
        v∈I ∧ M.IsMatching ∧ M.verts={u|u≠v} ∧ M.edgeSet.ncard=matchingEdges Q ∧
        ∃a b : ↥(Iᶜ : Set X), s.pivot=a.val ∧
          holeHeavy (Q.induce Iᶜ) (restrictedOutsideMatching Q I M) a ∧ (restrictedOutsideMatching Q I M).Adj a b := by
  obtain ⟨I,v,M,ind,largest,three,vi,hm,supp,opt,hn,max,gap,anti,a,b,heavy,ab,pair,dis,cl,off,cover,sep,shapes⟩ :=
    unpaid_exceptional_clique_partition Q D k six conn reg crit fail
  classical
  let N := restrictedOutsideMatching Q I M
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  let _ := Fintype.ofFinite J
  let F := exceptionalParts (Q.induce Iᶜ) N b
  have count : Fintype.card (Option J)=I.ncard := by
    rw [Fintype.card_option,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    exact gap
  have exp := regular_factorCritical_exposure Q crit v D reg
  have env := (envelope_reserve_account Q D).2
  have trunc := envelopeReserve_le_truncation Q D k (fun u => (reg u).le)
  have zero : baseReserve Q D=0 := by omega
  rcases shapes with ones|⟨q,order,others,two⟩
  · have positive := exceptional_singletons_positive Q I ind D (by omega) reg crit a F count
      dis off cover sep ones
    omega
  · obtain ⟨s,point,part⟩ := lift_exceptional_big_clique Q I D a F count dis off cover sep q (cl q) order others two
    exact ⟨I,ind,largest,three,s,v,M,vi,hm,supp,opt,a,b,point,heavy,ab⟩

#print axioms unpaid_requires_large_exceptional_clique
end JSP452Audit.StarHost
