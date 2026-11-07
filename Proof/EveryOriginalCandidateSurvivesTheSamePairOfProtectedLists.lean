import FixedCompleteListsRetainTheLostStarsAtEveryHeight
namespace JSP452Audit.StarHost
open SimpleGraph

def fixedHeadLoss (Z N l x:ℕ) := min Z (N/(x+1))-l

theorem fixed_lists_price_original_winner {A:Type*} [Finite A] (C:SimpleGraph A) {s t r j x y:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (l:ℕ) (pos:0<l)
    (win:WinsHeight n m r j x y) :
    widthAt n m r j≤widthAt (fixedCoreList C n l) (fixedCoreList C m l) (r+l) j+
      (l+fixedHeadLoss (matchingEdges C) (Nat.card A) l x+fixedHeadLoss (matchingEdges C) (Nat.card A) l y) := by
  let K := fixedCoreList C n l
  let V := fixedCoreList C m l
  obtain ⟨_,_,height,red,blue,span⟩ := win
  have kn := protected_demand_antitone n _ hn ((componentBudget C n).entries_antitone n hn) l
  have vm := protected_demand_antitone m _ hm ((componentBudget C m).entries_antitone m hm) l
  have redKept : 0<originalThresholdCount K x := by
    change 0<originalThresholdCount (protectedDemand n _ l) x
    rw [protected_demand_threshold n _ hn ((componentBudget C n).entries_antitone n hn)];omega
  have blueKept : 0<originalThresholdCount V y := by
    change 0<originalThresholdCount (protectedDemand m _ l) y
    rw [protected_demand_threshold m _ hm ((componentBudget C m).entries_antitone m hm)];omega
  have fit := actual_rectangle_le_column (r:=r+l) K V kn vm height redKept blueKept
  have a := fixed_core_threshold_loss C n hn l x
  have b := fixed_core_threshold_loss C m hm l y
  change originalThresholdCount n x≤originalThresholdCount K x+fixedHeadLoss (matchingEdges C) (Nat.card A) l x at a
  change originalThresholdCount m y≤originalThresholdCount V y+fixedHeadLoss (matchingEdges C) (Nat.card A) l y at b
  change widthAt n m r j≤widthAt K V (r+l) j+_
  omega

#print axioms fixed_lists_price_original_winner
end JSP452Audit.StarHost
