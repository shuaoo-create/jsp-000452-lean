import SevenStageTooShortToPay
namespace JSP452Audit.StarHost
open SimpleGraph

theorem seven_to_five_incidence_cost {X:Type*} [Finite X] (G:SimpleGraph X) (cap:∀x,Nat.card (G.neighborSet x)≤7)
    (E S:Set X) (full:∀x∈E,Nat.card (G.neighborSet x)=7)
    (low:∀x,Nat.card ((G.induce Sᶜ).neighborSet x)≤5) :
    2*E.ncard≤9*S.ncard := by
  classical
  let V := E \ S
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite S
  have lost (x:V) : 2≤(G.neighborSet x.val∩S).ncard := by
    let v : ↥(Sᶜ:Set X) := ⟨x.val,x.property.2⟩
    have remain := low v
    rw [induced_degree_intersection] at remain
    have dis : Disjoint (G.neighborSet x.val∩S) (G.neighborSet x.val∩Sᶜ) :=
      disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
    have all : (G.neighborSet x.val∩S)∪(G.neighborSet x.val∩Sᶜ)=G.neighborSet x.val := by
      rw [←Set.inter_union_distrib_left,Set.union_compl_self,Set.inter_univ]
    have count := Set.ncard_union_eq dis
    rw [all] at count
    change (G.neighborSet x.val∩Sᶜ).ncard≤5 at remain
    have deg : (G.neighborSet x.val).ncard=7 := full _ x.property.1
    omega
  have lower := Finset.sum_le_sum (s:=(Finset.univ:Finset V)) (fun x _ => lost x)
  rw [←crossCount_eq_neighbor_sum,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at lower
  have upper := Finset.sum_le_sum (s:=(Finset.univ:Finset S))
    (fun x _ => (Set.ncard_le_ncard (Set.inter_subset_left (s:=G.neighborSet x.val) (t:=V))).trans (cap x.val))
  rw [←crossCount_eq_neighbor_sum,crossCount_swap G S V,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at upper
  have total := Set.ncard_le_ncard_sdiff_add_ncard E S
  change V.ncard*2≤crossCount G V S at lower
  change crossCount G V S≤S.ncard*7 at upper
  change E.ncard≤V.ncard+S.ncard at total
  omega

#print axioms seven_to_five_incidence_cost
end JSP452Audit.StarHost
