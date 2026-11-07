import EveryUnpaidHighThirdGapHasTheActualSingleRegularException
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem third_gap_remaining_original_states (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    D=H+3 → ∃(K:DegreeRegion F.G D) (k c:ℕ) (P:ScaledPortPlan K k c),0<k ∧ Nonempty (PortGraphLayers P) ∧
      0<h ∧ h≤P.excess ∧ 8*P.gamma h+(3*(D:ℤ)+2)*P.excess+((D:ℤ)-10)*h+4*P.beta≤0 ∧
      (D%2=1 → h+1≤P.excess ∧ 8*P.gamma h+(3*(D:ℤ)+5)*P.excess+((D:ℤ)-9)*h+4*P.beta≤0) ∧
      P.capacity<2*(F.rank-matchingEdges F.G) ∧ P.capacity<peakCountAbove (F.G.induce P.exterior) (H-1) ∧
      (widthAt F.n F.m (F.r+P.cutRoots.ncard) (D-1)≤P.capacity ∨
        (D%2=0 ∧ h=1 ∧ P.excess=1 ∧ P.shortfall=0 ∧ (oddRegularComponents F.G D).ncard=1)) := by
  intro D H h gap
  obtain ⟨K,k,c,P,live,⟨E⟩,hp,rp,signed,odd,one⟩ := strict_third_gap_root_package F paid gap
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have credit : P.gamma h≤-(P.excess:ℤ) := by
    change 8*P.gamma h+(3*(D:ℤ)+2)*P.excess+((D:ℤ)-10)*h+4*P.beta≤0 at signed
    have a := mul_nonneg (show (0:ℤ)≤3*(D:ℤ)-6 by omega) (show (0:ℤ)≤P.excess by positivity)
    have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-10 by omega) (show (0:ℤ)≤h by positivity)
    linarith only [a,b,signed,show (0:ℤ)≤P.beta by positivity]
  obtain ⟨deficit,inventory⟩ := third_gap_initial_inventory F paid P E hp credit gap
  refine ⟨K,k,c,P,live,⟨E⟩,hp,rp,signed,odd,deficit,inventory,?_⟩
  by_cases low:widthAt F.n F.m (F.r+P.cutRoots.ncard) (D-1)≤P.capacity
  · exact Or.inl low
  · have single := third_gap_high_is_single F paid P E hp rp signed (fun a => (odd (by change D%2=1;omega)).2) gap (by change P.capacity<widthAt F.n F.m (F.r+P.cutRoots.ncard) (D-1);omega)
    obtain ⟨width,reg,zero⟩ := one single
    have even : D%2=0 := by
      by_contra! notEven
      have grow := (odd (by change D%2=1;omega)).1
      omega
    exact Or.inr ⟨even,width,single,zero,reg⟩

#print axioms third_gap_remaining_original_states
end JSP452Audit.StarHost
