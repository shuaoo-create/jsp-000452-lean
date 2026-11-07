import CubicResidualRemovalCost
import CriticalBarrier
import ActualRegionRanks
import CoreForestMass
namespace JSP452Audit.StarHost
open SimpleGraph
namespace CubicPairFamily
variable {X I : Type*} [Fintype X] [Fintype I] (P:CubicPairFamily X I)

/-- Tutte's barrier bounds the actual number of labelled edges, allowing
parallel pairs. The matching is taken in the graph supporting all pairs. -/
theorem labelled_edges_le_four_rank (G : SimpleGraph X) (edges : ∀i,G.Adj (P.left i) (P.right i))
    (cap : ∀v,P.degree Set.univ v≤3) : Fintype.card I≤4*matchingEdges G := by
  classical
  obtain ⟨S,tight,data⟩ := exists_critical_barrier G
  let H := G.induce Sᶜ
  let C := H.ConnectedComponent
  let _ := Fintype.ofFinite C
  let piece (c:C) : Set X := Subtype.val '' c.supp
  have full : P.active Set.univ=Finset.univ := by ext i;simp [mem_active]
  have removed := P.degree_removal (Set.univ:Set X) S (Set.subset_univ _)
  have complement : (Set.univ:Set X)\S=Sᶜ := by ext x;simp [Set.mem_sdiff]
  rw [complement,full,Finset.card_univ] at removed
  have rootCost := four_sum_mono S (P.degree Set.univ) _ (fun v _ => cap v)
  rw [four_sum_const] at rootCost
  have outer : Fintype.card I≤3*S.ncard+(P.active Sᶜ).card := by omega
  let J := ↥(P.active Sᶜ)
  let L (j:J) : ↥(Sᶜ : Set X) := ⟨P.left j.val,((P.mem_active _ _).1 j.property).1⟩
  let R (j:J) : ↥(Sᶜ : Set X) := ⟨P.right j.val,((P.mem_active _ _).1 j.property).2⟩
  let c (j:J) : C := H.connectedComponentMk (L j)
  let Z := Σcc:C,↥(P.active (piece cc))
  have pairIn (j:J) : j.val∈P.active (piece (c j)) := by
    apply (P.mem_active _ _).2
    have left : L j∈(c j).supp := rfl
    have right : R j∈(c j).supp := ((c j).mem_supp_congr_adj (show H.Adj (L j) (R j) from edges j.val)).1 left
    exact ⟨⟨L j,left,rfl⟩,⟨R j,right,rfl⟩⟩
  let sent (j:J) : Z := ⟨c j,⟨j.val,pairIn j⟩⟩
  have injection := Nat.card_le_card_of_injective sent (fun a b eq => Subtype.ext
    (congrArg (fun z:Z => z.2.val) eq))
  change Nat.card ↥(P.active Sᶜ)≤Nat.card (Σcc:C,↥(P.active (piece cc))) at injection
  rw [Nat.card_sigma] at injection
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe] at injection
  have per (cc:C) : (P.active (piece cc)).card≤4*matchingEdges cc.toSimpleGraph := by
    have count := factorCritical_order_rank cc.toSimpleGraph (data cc).2 cc.nonempty_supp.to_subtype.some
    have size : (piece cc).ncard=2*matchingEdges cc.toSimpleGraph+1 := by
      rw [show (piece cc).ncard=cc.supp.ncard from Set.ncard_image_of_injective _ Subtype.val_injective]
      exact (Nat.card_coe_set_eq _).symm.trans count
    have bound := four_sum_mono (piece cc) (P.degree (piece cc)) _ (fun x _ =>
      (P.degree_mono (Set.subset_univ _) x).trans (cap x))
    rw [P.sum_internal,four_sum_const,size] at bound
    by_cases pos : 0<matchingEdges cc.toSimpleGraph
    · omega
    have one : (piece cc).ncard≤1 := by omega
    have empty : P.active (piece cc)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun j z => by
      obtain ⟨a,b⟩ := (P.mem_active _ _).1 z
      exact P.distinct j ((Set.ncard_le_one (Set.toFinite _)).mp one _ a _ b))
    rw [empty,Finset.card_empty];omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun cc _ => per cc)
  rw [←Finset.mul_sum] at sum
  have gluing := (component_rank_budget_gluing H).1
  have all := tight_deletes_rank G S S tight Set.Subset.rfl
  change matchingEdges G=S.ncard+matchingEdges H at all
  change matchingEdges H=∑cc:C,matchingEdges cc.toSimpleGraph at gluing
  rw [←gluing] at sum
  omega

end CubicPairFamily
#print axioms CubicPairFamily.labelled_edges_le_four_rank
end JSP452Audit.StarHost
