import ZeroReserveNontrivialBlock
import FourNontrivialBlock
import UnpaidPreferredBlock
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- On an unpaid original connected component, even D≥4, the no-exception
case alone now suffices to obtain the connected preferred union. -/
theorem unpaid_even_no_exception_preferred (Q : SimpleGraph X) (D k : ℕ) (four : 4≤D) (conn : Q.Connected)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (fail : envelopeReserve Q k<minimumExposure Q D) :
    ∃ (I : Set X) (v : X) (M : Q.Subgraph),
      Q.IsIndepSet I ∧ (∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard) ∧ v∈I ∧
      M.IsMatching ∧ M.verts={x|x≠v} ∧ M.edgeSet.ncard=matchingEdges Q ∧
      let H := Q.induce Iᶜ
      let N := restrictedOutsideMatching Q I M
      let W := independentMateLabels Q I v M
      Subtype.val '' N.vertsᶜ=W ∧
      (exceptionalMateRegion H N=∅ →
        ∃w,w.val∈W ∧ w∉N.verts ∧ 3≤(mateBlock H N w).ncard ∧
          (H.induce (mateBlock H N w ∪ zeroMateRegion H N)).Connected ∧
          ∀u,u∉N.verts → u≠w → H.IsClique (mateBlock H N u)) := by
  obtain ⟨I,v,M,ind,largest,three,vi,m,supp,opt,hm,max,_,labels,count,_,anti,_⟩ :=
    unpaid_regular_mate_decomposition Q D k (by omega) reg crit fail
  refine ⟨I,v,M,ind,largest,vi,m,supp,opt,labels,?_⟩
  intro noEx
  let H := Q.induce Iᶜ
  let N := restrictedOutsideMatching Q I M
  have order := factorCritical_order_rank Q crit v
  have even := regular_even_on_odd Q D (show Odd (Nat.card X) from ⟨matchingEdges Q,by omega⟩) reg
  have exp := regular_factorCritical_exposure Q crit v D reg
  have env := (envelope_reserve_account Q D).2
  have trunc := envelopeReserve_le_truncation Q D k (fun u => (reg u).le)
  have zero : baseReserve Q D=0 := by omega
  have gap : N.vertsᶜ.ncard+1=I.ncard := by
    rwa [←labels,Set.ncard_image_of_injective _ Subtype.val_injective] at count
  have cl := (pullback_mate_antineighborhood_clique Q I N _ labels anti).subset (zeroMateRegion_subset_anti H N)
  have big : ∃ w,w∉N.verts ∧ 3≤(mateBlock H N w).ncard := by
    by_cases d4 : D=4
    · subst D;exact four_zero_reserve_has_nontrivial_block Q I conn ind largest three reg crit zero N hm max gap noEx cl
    · have six : 6≤D := by obtain ⟨j,h⟩ := even;omega
      exact zero_reserve_has_nontrivial_block Q I conn ind largest three D six even reg crit zero N hm max gap noEx cl
  obtain ⟨w,hw,large,joined,others⟩ :=
    exists_preferred_connected_block Q I ind largest D even reg N hm max gap noEx cl big
  exact ⟨w,labels ▸ ⟨w,hw,rfl⟩,hw,large,joined,others⟩

#print axioms unpaid_even_no_exception_preferred
end JSP452Audit.StarHost
