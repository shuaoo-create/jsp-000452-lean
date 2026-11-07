import EighthColumnOnTheActualSevenDegreeRemainder
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem live_row_height_at_degree_cap {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : 0<rowCount s t r) (cap : ∀x,Nat.card (G.neighborSet x)≤D) : diagonal n m (r+2)≤D+1 := by
  by_contra! high
  have elem : 0∈offsetsAt n m r (D+2) := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,by change D+2≤diagonal n m (r+2);omega⟩
  have pos : 0<widthAt n m r (D+2) := Finset.card_pos.mpr ⟨0,elem⟩
  have endAt := uniform_envelope_vanishes_above G D (D+1) cap (by omega)
  change uniformEnvelope G (D+2)=0 at endAt
  have width := widthAt_le_uniformEnvelope hs ht n m hn hm pn pm G r (D+2) row (by omega)
  omega

theorem exposure_edge_handshake {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) :
    D*minimumExposure G D≤2*G.edgeSet.ncard := by
  obtain ⟨M,_,_,opt⟩ := minimumExposure_attained G D
  let U := exposedFull G M D
  have sum := degree_sum_complement G U
  have full : originalDegreeSum G U=D*U.ncard := degree_sum_full G U D (fun _ h => h.2)
  change U.ncard=minimumExposure G D at opt
  rw [full,opt] at sum;omega

/-- Both deletions use the same original lists and actual graph sources.
The proof covers the case in which the second deletion exhausts the row. -/
theorem nine_two_stage_seven_exposure_ceiling (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (S T : Set F.X)
    (first : 0<S.ncard) (fit : S.ncard<F.rank) (later : S.ncard≤T.ncard)
    (cap1 : ∀v,Nat.card ((F.G.induce Sᶜ).neighborSet v)≤8)
    (cap2 : ∀v,Nat.card ((F.G.induce Tᶜ).neighborSet v)≤7)
    (fee1 : F.G.edgeSet.ncard+2≥(F.G.induce Sᶜ).edgeSet.ncard+9*S.ncard)
    (fee2 : (F.G.induce Sᶜ).edgeSet.ncard+2≥(F.G.induce Tᶜ).edgeSet.ncard+8*(T.ncard-S.ncard)) :
    minimumExposure (F.G.induce Tᶜ) 7≤9 := by
  let X1 := F.G.induce Sᶜ
  let X2 := F.G.induce Tᶜ
  let r1 := F.r+S.ncard
  let r2 := F.r+T.ncard
  let k := T.ncard-S.ncard
  let n := F.n
  let m := F.m
  let E1 := rowEnergy n m r1
  let E2 := rowEnergy n m r2
  have row1 := row_delete_set F.G S _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  have row2 := row_delete_set F.G T _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  have feasible : 0<rowCount F.s F.t r1 := by dsimp [r1,StrictFamily.rank,rowCount] at fit ⊢;omega
  have smaller1 : rowCount F.s F.t r1<F.rank := by dsimp [r1,StrictFamily.rank,rowCount] at fit ⊢;omega
  have peak1 := live_row_height_at_degree_cap X1 F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row1 feasible cap1
  have price1 := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm X1 r1 8 F.rank (by decide)
    row1 feasible smaller1 paid cap1 peak1
  norm_num at price1
  have prefix1 := prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r S.ncard F.live
  rw [nine] at prefix1
  have strict := F.strict
  have narrow := (strict_nine_original_peak F paid nine).2.1
  change rowEnergy F.n F.m F.r≤E1+9*S.ncard+highestWidth F.n F.m F.r at prefix1
  change X1.edgeSet.ncard+9*S.ncard≤F.G.edgeSet.ncard+2 at fee1
  have v1 : X1.edgeSet.ncard≤E1+3 := by omega
  change 6*(minimumExposure X1 8:ℤ)≤40+2*((X1.edgeSet.ncard:ℤ)-E1) at price1
  have rho1 : minimumExposure X1 8≤7 := by omega
  have col := widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm X1 r1 9 row1 (by decide)
  have exp := (uniformEnvelope_le_deletion X1 8 (by decide)).trans (deletionBudget_le_minimumExposure X1 8 (by decide) cap1)
  change uniformEnvelope X1 9≤minimumExposure X1 8 at exp
  have top : widthAt F.n F.m r1 9≤7 := by omega
  have cut := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm r1 k 8 peak1
  have join : r1+k=r2 := by dsimp [r1,r2,k];omega
  rw [join] at cut
  change E1≤E2+8*k+widthAt F.n F.m r1 9 at cut
  change X2.edgeSet.ncard+8*k≤X1.edgeSet.ncard+2 at fee2
  have v2 : X2.edgeSet.ncard≤E2+12 := by omega
  change minimumExposure X2 7≤9
  by_cases live : 0<rowCount F.s F.t r2
  · have smaller2 : rowCount F.s F.t r2<F.rank := by dsimp [r1,r2,StrictFamily.rank,rowCount] at smaller1 ⊢;omega
    have peak2 := live_row_height_at_degree_cap X2 F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row2 live cap2
    have price := smaller_row_seven_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm X2 r2 F.rank row2 live smaller2 paid cap2 peak2
    change 5*(minimumExposure X2 7:ℤ)≤24+2*((X2.edgeSet.ncard:ℤ)-E2) at price
    omega
  · have empty : E2=0 := by dsimp only [E2,n,m,rowEnergy];simp [Nat.eq_zero_of_not_pos live]
    have bound := exposure_edge_handshake X2 7
    omega

#print axioms live_row_height_at_degree_cap
#print axioms exposure_edge_handshake
#print axioms nine_two_stage_seven_exposure_ceiling
end JSP452Audit.StarHost
