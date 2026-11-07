import OddAndEvenFactorCutsUseTheOriginalRootDegrees
namespace JSP452Audit.StarHost.PortGraphLayers
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D} {P:ScaledPortPlan K k c} (E:PortGraphLayers P)

theorem selected_side_degree_price (cap:∀x,Nat.card (G.neighborSet x)≤D) (S:Set X) :
    c*originalDegreeSum G S+(∑t:Fin k,originalDegreeSum (E.graph t) S)≤(c*D+k)*S.ncard := by
  classical
  have bound (x:X) : c*(G.neighborSet x).ncard+(∑t:Fin k,((E.graph t).neighborSet x).ncard)≤c*D+k := by
    have val := E.budget x
    simp only [Nat.card_coe_set_eq] at val
    have exact := Nat.sub_add_cancel (cap x)
    change D-(G.neighborSet x).ncard+(G.neighborSet x).ncard=D at exact
    have mult := congrArg (fun z => c*z) exact
    change c*((D-(G.neighborSet x).ncard)+(G.neighborSet x).ncard)=c*D at mult
    rw [Nat.mul_add] at mult;omega
  have sum := Finset.sum_le_sum (s:=S.toFinite.toFinset) (fun x _ => bound x)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_comm (s:=S.toFinite.toFinset),Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at sum
  have size := (Set.ncard_eq_toFinset_card S S.toFinite).symm
  rw [size,Nat.mul_comm S.ncard (c*D+k)] at sum
  exact sum

theorem complementary_layer_price (live:0<D) (cap:∀x,Nat.card (G.neighborSet x)≤D) (T:Set X) (t:Fin k) :
    originalDegreeSum (G \ E.graph t) T≤(D-1)*T.ncard+(T∩E.missing t).ncard := by
  classical
  let R := E.graph t
  let U := E.missing t
  have per (x:X) : ((G \ R).neighborSet x).ncard≤D-1+(if x∈U then 1 else 0) := by
    have split := palette_neighbor_sum G R (E.sub t) x
    have lim : (G.neighborSet x).ncard≤D := cap x
    by_cases full:Nat.card (G.neighborSet x)=D
    · have exact := E.full t x full
      by_cases hit:x∈U
      · rw [if_pos hit];omega
      · rw [if_neg hit];have val := exact.2 hit;change (R.neighborSet x).ncard=1 at val;omega
    · change (G.neighborSet x).ncard≠D at full;split_ifs <;> omega
  have sum := Finset.sum_le_sum (s:=T.toFinite.toFinset) (fun x _ => per x)
  rw [Finset.sum_add_distrib,subset_indicator_sum,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,
    ←Set.ncard_eq_toFinset_card T T.toFinite,Nat.mul_comm T.ncard (D-1)] at sum
  exact sum

theorem all_layers_matching_cut (p q:ℕ) (deg:p+q=D) (odd:Odd p) (live:0<D)
    (cap:∀x,Nat.card (G.neighborSet x)≤D) (S T:Set X) (apart:Disjoint S T) :
    k*((uniformOddPieces G p q S T).ncard+crossCount G T S)≤
      (∑t:Fin k,originalDegreeSum (E.graph t) S)+k*((D-1)*T.ncard)+(∑t:Fin k,(E.missing t).ncard) := by
  classical
  have per (t:Fin k) := layer_tokens_on_one_factor_cut odd (fun x => (cap x).trans_eq deg.symm) S T apart
    (E.graph t) (E.sub t) (E.missing t) (fun x full => E.full t x (full.trans deg))
  have both (t:Fin k) : (T∩E.missing t).ncard+(E.missing t\(S∪T)).ncard≤(E.missing t).ncard := by
    let U := E.missing t
    have d : Disjoint (T∩U) (U\(S∪T)) := Set.disjoint_left.mpr (fun _ tm um => um.2 (Or.inr tm.1))
    rw [←Set.ncard_union_eq d];exact Set.ncard_le_ncard (Set.union_subset Set.inter_subset_right Set.sdiff_subset)
  have one (t:Fin k) : (uniformOddPieces G p q S T).ncard+crossCount G T S≤
      originalDegreeSum (E.graph t) S+(D-1)*T.ncard+(E.missing t).ncard := by
    have f := E.complementary_layer_price live cap T t;have g := both t;have e := per t;omega
  have bill := Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin k))) (fun t _ => one t)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_add] using bill

#print axioms selected_side_degree_price
#print axioms complementary_layer_price
#print axioms all_layers_matching_cut
end JSP452Audit.StarHost.PortGraphLayers
