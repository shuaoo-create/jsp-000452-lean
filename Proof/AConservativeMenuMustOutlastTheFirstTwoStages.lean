import TheSignedTenthColumnAfterTheSameFullDegreeDeletion
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_menu_prices_on_budget_support {I:Type*} [Fintype I] [DecidableEq I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (K:TenRegularBudget F.G) (e:I↪F.G.ConnectedComponent) (sel:Finset.univ.map e=K.selected)
    (z:I→ℕ) (ranks:∀i,matchingEdges (e i).toSimpleGraph≤z i) (budget:(∑i,z i)=K.P)
    (k:ℕ) (menu:SplitCapacities z (F.r+k))
    (B:Set ↥(K.supportᶜ:Set F.X)) (first:CompleteDegreeStage (F.G.induce K.supportᶜ) 10 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce K.supportᶜ).induce Bᶜ) 9 C)
    (fit:k≤B.ncard+C.ncard) :
    K.P+5*K.eps+1+min k B.ncard≤widthAt F.n F.m F.r 10+highestWidth F.n F.m F.r ∧
      5*K.eps+1+min k B.ncard≤k+highestWidth F.n F.m F.r := by
  have fees := ten_nine_whole_menu_prices F paid ten K e sel z ranks budget k menu
  rw [sel] at fees
  exact fees B first C second fit

theorem ten_menu_outlasts_high_stages {I:Type*} [Fintype I] [DecidableEq I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (K:TenRegularBudget F.G) (e:I↪F.G.ConnectedComponent) (sel:Finset.univ.map e=K.selected)
    (z:I→ℕ) (ranks:∀i,matchingEdges (e i).toSimpleGraph≤z i) (budget:(∑i,z i)=K.P)
    (k:ℕ) (menu:SplitCapacities z (F.r+k))
    (B:Set ↥(K.supportᶜ:Set F.X)) (first:CompleteDegreeStage (F.G.induce K.supportᶜ) 10 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce K.supportᶜ).induce Bᶜ) 9 C)
    (u:ℕ) (reserve:∃A:Set ↥K.support,CompleteDegreeStage (F.G.induce K.support) 10 A ∧ A.ncard+u≤K.P)
    (high:highestWidth F.n F.m F.r≤5*K.eps)
    (cost:highestWidth F.n F.m F.r+(38+2*highestWidth F.n F.m F.r)/7≤5*K.eps+u) :
    B.ncard+C.ncard<k := by
  by_contra! fits
  have fees := ten_menu_prices_on_budget_support F paid ten K e sel z ranks budget k menu B first C second fits
  obtain ⟨A,inner,room⟩ := reserve
  have bill := (ten_closed_stage_width F paid ten K A inner B first).2
  change widthAt F.n F.m F.r 10≤A.ncard+B.ncard+(38+2*highestWidth F.n F.m F.r)/7 at bill
  by_cases inside:k≤B.ncard
  · rw [min_eq_left inside] at fees;omega
  · rw [min_eq_right (by omega : B.ncard≤k)] at fees;omega

#print axioms ten_menu_prices_on_budget_support
#print axioms ten_menu_outlasts_high_stages
end JSP452Audit.StarHost
