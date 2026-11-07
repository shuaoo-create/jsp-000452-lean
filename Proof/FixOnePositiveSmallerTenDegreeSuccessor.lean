import TheOneAndTwoComponentHeadBoundsAndCapacity
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_prefix_three_columns {s t r:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (top:diagonal n m (r+2)=11) (k:ℕ) :
    rowEnergy n m r≤rowEnergy n m (r+k)+8*k+widthAt n m r 9+widthAt n m r 10+highestWidth n m r := by
  let p := min k (rowCount s t r)
  let A := offsetsAt n m r 9
  let B := offsetsAt n m r 10
  let C := offsetsAt n m r 11
  have each (i:ℕ) (hi:i∈Finset.range p) : diagonal n m (r+i+2)≤
      8+(if i∈A then 1 else 0)+(if i∈B then 1 else 0)+(if i∈C then 1 else 0) := by
    have live := (Finset.mem_range.mp hi).trans_le (Nat.min_le_right k (rowCount s t r))
    have dom := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+i by omega)
      (show r+i<s+t-1 by dsimp [rowCount] at live;omega)
    have a : i∈A ↔ 9≤diagonal n m (r+i+2) := by simp [A,offsetsAt,live]
    have b : i∈B ↔ 10≤diagonal n m (r+i+2) := by simp [B,offsetsAt,live]
    have c : i∈C ↔ 11≤diagonal n m (r+i+2) := by simp [C,offsetsAt,live]
    simp only [a,b,c]
    split_ifs <;> omega
  have total := Finset.sum_le_sum each
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,Finset.sum_boole] at total
  have count (j:ℕ) : ((Finset.range p).filter fun i => i∈offsetsAt n m r j).card≤widthAt n m r j :=
    Finset.card_le_card (fun _ h => (Finset.mem_filter.mp h).2)
  have ac := count 9
  change ((Finset.range p).filter fun i => i∈A).card≤widthAt n m r 9 at ac
  have bc := count 10
  have cc := count 11
  change ((Finset.range p).filter fun i => i∈B).card≤widthAt n m r 10 at bc
  change ((Finset.range p).filter fun i => i∈C).card≤widthAt n m r 11 at cc
  rw [←top,width_at_actual_top hs ht n m hn hm] at cc
  have parts := rowEnergy_prefix_split n m r k
  change rowEnergy n m r=(∑i∈Finset.range p,diagonal n m (r+i+2))+_ at parts
  have lim : p≤k := Nat.min_le_left _ _
  omega



namespace PricedTenMenu
variable {F:StrictFamily.{u}} (A:PricedTenMenu F)
noncomputable def steps := Finset.univ.sup A.units-(F.r+1)

theorem step_menu [DecidableEq ↥A.K.selected] : SplitCapacities A.units (F.r+A.steps) := by
  apply split_capacities_of_small
  intro i
  have sup := Finset.le_sup (f:=A.units) (Finset.mem_univ i)
  dsimp only [steps];omega

theorem step_bounds (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (cost:6*highestWidth F.n F.m F.r≤13*A.K.eps+6) :
    A.steps≤2*(F.rank-matchingEdges F.G) ∧ A.steps<A.K.P ∧ 0<rowCount F.s F.t (F.r+A.steps+A.K.P) ∧
      rowCount F.s F.t (F.r+A.steps+A.K.P)<F.rank := by
  classical
  obtain ⟨_,_,volume,each⟩ := ten_regular_small_heads_fit_two_deficits F paid ten A cost
  have sup := Finset.sup_le (s:=Finset.univ) (fun i (_:i∈Finset.univ) => each i)
  have all : Finset.univ.sup A.units≤A.K.P := Finset.sup_le (fun i _ =>
    (Finset.single_le_sum (f:=A.units) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq A.total)
  have progress := A.K.minimum_order
  have pos := (ten_conservative_forest_endpoints F paid ten A.K).1
  have adj := A.K.exposed_in_original
  have bounds := (ten_closed_endpoint_sizes F paid ten A.K).1
  let d := F.rank-matchingEdges F.G
  let Q := matchingEdges (F.G.induce A.K.support)
  change Q+F.r+2*d≤min F.s F.t at bounds
  have s := bounds.trans (Nat.min_le_left _ _)
  have t := bounds.trans (Nat.min_le_right _ _)
  change A.K.slack+A.K.eps+1≤d-A.K.slack at pos
  have fit : Q≤A.K.P := A.K.fits
  have exactSlack : A.K.slack=A.K.P-Q := rfl
  have size : F.rank=F.s+F.t-1-F.r := rfl
  change Finset.univ.sup A.units≤2*d at sup
  change A.steps≤2*d ∧ A.steps<A.K.P ∧ 0<F.s+F.t-1-(F.r+A.steps+A.K.P) ∧ F.s+F.t-1-(F.r+A.steps+A.K.P)<F.rank
  dsimp only [steps];omega

theorem physical_stage_prefix (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (cost:6*highestWidth F.n F.m F.r≤13*A.K.eps+6)
    (H:ThreeDegreeStages (F.G.induce A.K.supportᶜ) 8) :
    H.midCut.ncard<A.steps ∧
    ((0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8) → A.steps≤H.lastCut.ncard) := by
  classical
  have price := A.outlast F paid ten A.steps A.step_menu H.upper H.first H.middle H.second
  have count := nested_removed_card H.upper H.middle
  change H.midCut.ncard=H.upper.ncard+H.middle.ncard at count
  refine ⟨by omega,?_⟩
  intro heads
  have cap (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card ((F.G.induce A.K.supportᶜ).neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  have tail := (H.degree_caps cap).2.2
  have size := (ten_closed_endpoint_sizes F paid ten A.K).2 H.lastCut 8 (by decide) tail heads
  exact (A.step_bounds paid ten cost).1.trans size

end PricedTenMenu
#print axioms ten_prefix_three_columns
#print axioms PricedTenMenu.step_menu
#print axioms PricedTenMenu.step_bounds
#print axioms PricedTenMenu.physical_stage_prefix
end JSP452Audit.StarHost
