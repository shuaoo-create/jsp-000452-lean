import TwoActualNinePortAreaAccounts
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- This comparison needs only the actual budget list and its fixed joined
residual. No graph decomposition is encoded in its numerical conclusion. -/
theorem missing_threshold_of_two_budget_columns {s t r j a P : ℕ}
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i)
    (W : RemovalBudget s) (fit : W.loss≤P) (live : 0<W.len)
    (loss : a+2*P+widthAt (W.entries n) m (r+a) j+widthAt (commonErasedDemand n W a P) m r j<2*widthAt n m r j) :
    ∀x y,WinsHeight n m r j x y →
      2≤x ∧ originalThresholdCount (commonErasedDemand n W a P) x=0 ∧
      originalThresholdCount n x≤P ∧ originalThresholdCount (W.entries n) x≤a := by
  let J := commonErasedDemand n W a P
  change a+2*P+widthAt (W.entries n) m (r+a) j+widthAt J m r j<2*widthAt n m r j at loss
  intro x y win
  obtain ⟨px,_,height,_,right,area⟩ := win
  obtain ⟨_,nJ,LJ,JL⟩ := common_threshold_floors n hn pn W a P x fit
  change originalThresholdCount n x≤P+originalThresholdCount J x at nJ
  change originalThresholdCount (W.entries n) x≤a+originalThresholdCount J x at LJ
  change originalThresholdCount J x≤originalThresholdCount (W.entries n) x at JL
  have zero : originalThresholdCount J x=0 := by
    by_contra! present
    have posJ : 0<originalThresholdCount J x := by omega
    have posL := posJ.trans_le JL
    have left := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm height posL right
    have kept := actual_rectangle_le_column (r:=r) J m (common_erased_antitone n hn W a P) hm height posJ right
    omega
  have units : originalThresholdCount J 1=W.len := original_threshold_one J (common_erased_positive n W a P)
  have nonunit : 2≤x := by
    by_contra! low
    have eq : x=1 := by omega
    rw [eq,units] at zero
    omega
  exact ⟨nonunit,zero,by omega,by omega⟩

namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)
noncomputable abbrev basicPrice {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r j : ℕ) :=
  let W := componentBudget (G.induce R.chosen) n
  R.roots.ncard+2*R.totalCapacity+widthAt (W.entries n) m (r+R.roots.ncard) j+
    widthAt (commonErasedDemand n W R.roots.ncard R.totalCapacity) m r j

theorem basic_price_sum {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) :
    let W := componentBudget (G.induce R.chosen) n
    (∑j∈Finset.range 8,R.basicPrice n m r (j+2))=8*(R.roots.ncard+2*R.totalCapacity)+
      interiorArea (W.entries n) m (r+R.roots.ncard) 9+
      interiorArea (commonErasedDemand n W R.roots.ncard R.totalCapacity) m r 9 := by
  intro W
  dsimp only [basicPrice]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp [interiorArea,W]
end NinePortRegion

theorem strict_nine_single_short_missing_column (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (long : R.totalCapacity<F.s) :
    ∃j,2≤j ∧ j≤9 ∧ R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j ∧
      (∃x y,WinsHeight F.n F.m F.r j x y) ∧
      ∀x y,WinsHeight F.n F.m F.r j x y →
        2≤x ∧ originalThresholdCount (commonErasedDemand F.n (componentBudget (F.G.induce R.chosen) F.n)
          R.roots.ncard R.totalCapacity) x=0 ∧
        originalThresholdCount F.n x≤R.totalCapacity ∧
        originalThresholdCount ((componentBudget (F.G.induce R.chosen) F.n).entries F.n) x≤R.roots.ncard := by
  have area := strict_nine_joint_residual_area F paid nine R long
  let W := componentBudget (F.G.induce R.chosen) F.n
  have narrow := (strict_nine_original_peak F paid nine).2.1
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have debt := (R.root_deleted_edge_account cap).2
  have positive := R.exposure
  have cheap : R.rootDebt≤5 := by omega
  have find : ∃j,2≤j ∧ j≤9 ∧ R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j := by
    by_contra! no
    have sum := Finset.sum_le_sum (s:=Finset.range 8) (fun i mem => no (i+2) (by omega)
      (by have := Finset.mem_range.mp mem;omega))
    rw [←Finset.mul_sum,R.basic_price_sum] at sum
    change 2*interiorArea F.n F.m F.r 9≤_ at sum
    omega
  obtain ⟨j,lo,hi,unpaid⟩ := find
  have live := (nine_long_side_actual_source_prices F paid nine R long).1
  have fit := (nine_long_side_actual_source_prices F paid nine R long).2.2.1
  have lost := missing_threshold_of_two_budget_columns F.n F.m F.hn F.hm F.pn W fit live unpaid
  have present : 0<widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,pa,pb,height,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) present
  exact ⟨j,lo,hi,unpaid,⟨x,y,pa,pb,height,red,blue,w⟩,lost⟩

#print axioms missing_threshold_of_two_budget_columns
#print axioms NinePortRegion.basic_price_sum
#print axioms strict_nine_single_short_missing_column
end JSP452Audit.StarHost
