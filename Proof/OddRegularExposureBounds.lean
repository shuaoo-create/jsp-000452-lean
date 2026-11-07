import BalancedCutGlobalOddRegularCount
import ExposureComponentSum
import EnvelopeComponentSum
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_exposure_order_rank {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (reg : ∀x, Nat.card (G.neighborSet x)=D) :
    2*matchingEdges G+minimumExposure G D=Nat.card X := by
  obtain ⟨M,hm,max,att⟩ := minimumExposure_attained G D
  have all : exposedFull G M D=M.vertsᶜ := by
    ext x
    change (x∉M.verts ∧ Nat.card (G.neighborSet x)=D) ↔ x∉M.verts
    simp [reg]
  rw [←max,←att,all,←matching_vertices_eq_twice_edges hm]
  exact Set.ncard_add_ncard_compl M.verts

theorem odd_regular_count_le_exposure {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) :
    (oddRegularComponents G D).ncard≤minimumExposure G D := by
  classical
  let := Fintype.ofFinite G.ConnectedComponent
  let Z := oddRegularComponents G D
  have one (c:G.ConnectedComponent) (h:c∈Z) : 1≤minimumExposure c.toSimpleGraph D := by
    obtain ⟨⟨k,odd⟩,full⟩ := h
    have eq := regular_exposure_order_rank c.toSimpleGraph D (fun x =>
      (component_degree_eq G c x).trans (full x.val x.property))
    change Nat.card c.supp=2*k+1 at odd
    change 2*matchingEdges c.toSimpleGraph+minimumExposure c.toSimpleGraph D=Nat.card c.supp at eq
    omega
  rw [minimumExposure_component_total]
  have count := Finset.sum_le_sum (s := (Finset.univ : Finset G.ConnectedComponent))
    (f := fun c => if c∈Z then 1 else 0) (g := fun c => minimumExposure c.toSimpleGraph D)
    (fun c _ => by split_ifs with h; exact one c h; exact Nat.zero_le _)
  simpa [Finset.sum_boole,Set.ncard_eq_toFinset_card'] using count

theorem strict_six_real_component_bounds (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (six : diagonal F.n F.m (F.r+2)-1=6) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 6).ncard
    let ρ := minimumExposure F.G 6
    1≤h ∧ h≤c ∧ c≤ρ ∧ ρ≤5 ∧ (ρ=5 → 4≤h) := by
  intro h c ρ
  obtain ⟨K⟩ := degreeRegion_exists F.G (diagonal F.n F.m (F.r+2)-1)
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).1
  have count := strict_six_original_odd_regular F paid six
  have exposure := odd_regular_count_le_exposure F.G 6
  have budget := strict_source_region_root_budget F paid K
  dsimp only at budget
  let D := diagonal F.n F.m (F.r+2)-1
  have slack : D*minimumExposure F.G D+2≤2*h+2*(D/2)*(D/2+1) := by
    change D*minimumExposure F.G D+_+_+_+2≤2*h+2*(D/2)*(D/2+1) at budget
    clear * - budget
    omega
  have eqD : D=6 := six
  rw [eqD] at slack
  change 6*ρ+2≤2*h+24 at slack
  change h≤c at count
  change c≤ρ at exposure
  refine ⟨width,count,exposure,?_,?_⟩ <;> omega

#print axioms regular_exposure_order_rank
#print axioms odd_regular_count_le_exposure
#print axioms strict_six_real_component_bounds
end JSP452Audit.StarHost
