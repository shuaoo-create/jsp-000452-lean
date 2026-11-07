import FiveDegreeActualWidth
import WholeCorePrice
namespace JSP452Audit.StarHost
universe u

theorem width_at_actual_top {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) :
    widthAt n m r (diagonal n m (r+2))=highestWidth n m r := by
  unfold widthAt highestWidth offsetsAt highestOffsets
  congr 1;apply Finset.filter_congr
  intro j hj
  have small := Finset.mem_range.mp hj
  have live : r+j<s+t-1 := by dsimp [rowCount] at small;omega
  have cap := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+j by omega) live
  omega

theorem strict_source_selector_ceiling (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    selectorTarget F.G D+1≤(highestWidth F.n F.m F.r:ℤ) := by
  intro D
  have large : 3≤D := strict_source_degree_at_least_three F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have hpos := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).1
  by_cases yes : 0<selectorTarget F.G D
  · have price := selector_positive_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r D F.rank
      F.row F.live le_rfl paid cap top.le yes
    rw [←top,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at price
    have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
    omega
  omega

theorem five_degree_strict_exposure_bounds (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (five : diagonal F.n F.m (F.r+2)-1=5) :
    let h := highestWidth F.n F.m F.r
    let ρ := minimumExposure F.G 5
    1≤h ∧ h≤ρ ∧ 5*ρ≤2*h+10 ∧ ρ<h+2 ∧ ρ≤3 := by
  intro h ρ
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  rw [five] at width
  change 1≤h ∧ h≤ρ at width
  have upper := strict_source_selector_ceiling F paid
  rw [five] at upper
  change ((5*(ρ:ℤ)+1)/2-6)+1≤(h:ℤ) at upper
  omega

/-- All hypotheses for the remaining signed-exposure step live on the same
strict host and the same exact-width, positive-multiplicity forced pair. -/
theorem five_degree_small_heads_frontier (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (five : diagonal F.n F.m (F.r+2)-1=5) (red : F.n ⟨0,F.hs⟩<5) (blue : F.m ⟨0,F.ht⟩<5) :
    ∃p q:ℕ,0<p ∧ 0<q ∧ p+q-1=highestWidth F.n F.m F.r ∧
      Forces F.G (forest (fun _ : Fin p => 4)) (forest (fun _ : Fin q => 3)) ∧
      (∀x,Nat.card (F.G.neighborSet x)≤5) ∧ minimumExposure F.G 5<p+q-1+2 ∧ minimumExposure F.G 5≤3 := by
  obtain ⟨p,q,hp,hq,width,forced⟩ := five_degree_uniform_obstruction F five red blue
  obtain ⟨_,_,_,upper,small⟩ := five_degree_strict_exposure_bounds F paid five
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  rw [five] at cap
  exact ⟨p,q,hp,hq,width,forced,cap,width.symm ▸ upper,small⟩

#print axioms width_at_actual_top
#print axioms strict_source_selector_ceiling
#print axioms five_degree_strict_exposure_bounds
#print axioms five_degree_small_heads_frontier
end JSP452Audit.StarHost
