import TheOnlyRemainingGapHasATrueTwoSidedTopWidthAtAnyWinningHead
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_one_deficit_with_one_actual_refund (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) (t gain:ℕ) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let d := F.rank-matchingEdges F.G
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let N := P.paidCore.ncard
    let Z := P.capacity
    let ρ := P.excess
    let e := minimumExposure (F.G.induce P.paidCore) D
    let G := P.gamma (highestWidth F.n F.m F.r)
    let L (j:ℕ) := widthAt F.n F.m r (j+2)-uniformEnvelope Y (j+2)
    D=H+1 → t < D-2 →
    (gain=0 ∨ 2*L t+2*gain≤2*Z+(if t=1 then ρ else 0)) →
    (2:ℤ)*Z+2*gain+2≤2*d+2*((N/3:ℕ):ℤ)+2*e+ρ+2*G := by
  intro D H d Y r N Z ρ e G L gap valid bonus
  let k₀ := D-2
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨sz,_,fit,_,_,_,_⟩ := full_capacity_prefix_data F paid P E hp credit
  have root := P.positive_count_with_original_roots E
  have per (j:ℕ) : 2*L j≤2*Z+(if j=1 then P.excess else 0) := by
    by_cases active:0<widthAt F.n F.m r (j+2)
    · obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<j+2) active
      have win : WinsHeight F.n F.m r (j+2) x y := w
      have inv := (strict_exterior_typed_column_inventory F paid P win).2.1
      change widthAt F.n F.m r (j+2)-actualCoordinateLoss Z N r x y≤uniformEnvelope Y (j+2) at inv
      have bound := true_third_gap_taxes Z N P.positives.ncard P.excess r x y fit sz (by dsimp only [r];omega) win.1 win.2.1
      have ht := win.2.2.1
      simp only [show x+y=4 ↔ j=1 by omega] at bound
      dsimp only [L];omega
    · have zero : L j=0 := by dsimp only [L];omega
      simp [zero]
  have perExtra (j:ℕ) : 2*L j+(if j=t then 2*gain else 0)≤2*Z+(if j=1 then ρ else 0) := by
    have usual := per j
    change 2*L j≤2*Z+(if j=1 then ρ else 0) at usual
    by_cases eq:j=t
    · subst j
      rw [if_pos rfl]
      rcases bonus with no|yes
      · simpa [no] using usual
      · exact yes
    · simpa [eq] using usual
  have sum := Finset.sum_le_sum (s:=Finset.range k₀) (fun j _ => perExtra j)
  have bonusSum : (∑j∈Finset.range k₀,if j=t then 2*gain else 0)=2*gain := by simp [show t<k₀ from valid]
  have exc : (∑j∈Finset.range k₀,if j=1 then ρ else 0)=ρ := by simp [show 1<k₀ by dsimp only [k₀];omega]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,exc,bonusSum,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at sum
  have top := (gap_one_top_typed F paid P E kl gap).2.2.2.1
  change widthAt F.n F.m r D≤uniformEnvelope Y D+N/3+e at top
  have last : L k₀≤N/3+e := by dsimp only [L];rw [show k₀+2=D by dsimp only [k₀];omega];omega
  have vol := original_exterior_deficit_volume F paid P D rfl L (by intro j _;dsimp only [L,r,Y];omega)
  change (D:ℤ)*Z+1≤(Z:ℤ)+d+(∑j∈Finset.range (D-1),L j:ℕ)+G at vol
  rw [show D-1=k₀+1 by dsimp only [k₀];omega,Finset.sum_range_succ] at vol
  have mult : D*Z=k₀*Z+2*Z := by conv_lhs => rw [show D=k₀+2 by dsimp only [k₀];omega,Nat.add_mul]
  omega

#print axioms gap_one_deficit_with_one_actual_refund
end JSP452Audit.StarHost