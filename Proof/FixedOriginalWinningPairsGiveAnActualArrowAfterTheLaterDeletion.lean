import PriceTheTrueThirdGapPrefixIncludingEveryExtraEdge
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem fixed_winner_typed_after_prefix {A B:Type u} [Finite A] [Finite B] (X:SimpleGraph A) (C:SimpleGraph B)
    {s t r j x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (l i:ℕ) (lp:0<l) (win:WinsHeight n m r j x y)
    (row:ForcingRow X (min s ((componentBudget C n).len+l)) (min t ((componentBudget C m).len+l))
      (padDemand (fixedCoreList C n l)) (padDemand (fixedCoreList C m l)) (r+i+l)) :
    let K := fixedCoreList C n l
    let V := fixedCoreList C m l
    let w := originalThresholdCount K x+originalThresholdCount V y-1-(r+i+l)
    ExactTypedWidth X x y w ∧ w≤widthAt K V (r+i+l) j ∧ widthAt n m r j≤
      w+i+l+fixedHeadLoss (matchingEdges C) (Nat.card B) l x+fixedHeadLoss (matchingEdges C) (Nat.card B) l y := by
  intro K V w
  obtain ⟨_,_,ht,red,blue,span⟩ := win
  have kn := protected_demand_antitone n _ hn ((componentBudget C n).entries_antitone n hn) l
  have vm := protected_demand_antitone m _ hm ((componentBudget C m).entries_antitone m hm) l
  have redKept : 0<originalThresholdCount K x := by
    change 0<originalThresholdCount (protectedDemand n _ l) x
    rw [protected_demand_threshold n _ hn ((componentBudget C n).entries_antitone n hn)];omega
  have blueKept : 0<originalThresholdCount V y := by
    change 0<originalThresholdCount (protectedDemand m _ l) y
    rw [protected_demand_threshold m _ hm ((componentBudget C m).entries_antitone m hm)];omega
  have a := fixed_core_threshold_loss C n hn l x
  have b := fixed_core_threshold_loss C m hm l y
  change originalThresholdCount n x≤originalThresholdCount K x+fixedHeadLoss (matchingEdges C) (Nat.card B) l x at a
  change originalThresholdCount m y≤originalThresholdCount V y+fixedHeadLoss (matchingEdges C) (Nat.card B) l y at b
  refine ⟨typed_width_of_original_rectangle X K V kn vm redKept blueKept row,actual_rectangle_le_column K V kn vm ht redKept blueKept,?_⟩
  dsimp only [w];omega

theorem third_gap_fixed_head_bounds {A B:Type u} [Finite A] [Finite B] (X:SimpleGraph A) (C:SimpleGraph B)
    {s t r j x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (i:ℕ) (lp:0<Nat.card B/5) (win:WinsHeight n m r j x y) (high:matchingEdges C<widthAt n m r j)
    (heads:3≤x ∧ 3≤y ∧ (4≤x ∨ 4≤y))
    (row:ForcingRow X (min s ((componentBudget C n).len+Nat.card B/5)) (min t ((componentBudget C m).len+Nat.card B/5))
      (padDemand (fixedCoreList C n (Nat.card B/5))) (padDemand (fixedCoreList C m (Nat.card B/5))) (r+i+Nat.card B/5)) :
    let N := Nat.card B
    let K := fixedCoreList C n (N/5)
    let V := fixedCoreList C m (N/5)
    ∃w,ExactTypedWidth X x y w ∧ w≤widthAt K V (r+i+N/5) j ∧
      matchingEdges C+1≤w+i+N/4 ∧ (4≤x → 4≤y → matchingEdges C+1≤w+i+N/5) := by
  intro N K V
  let l := N/5
  let w := originalThresholdCount K x+originalThresholdCount V y-1-(r+i+l)
  obtain ⟨actual,bound,price⟩ := fixed_winner_typed_after_prefix X C n m hn hm l i lp win row
  change widthAt n m r j≤w+i+l+fixedHeadLoss (matchingEdges C) N l x+fixedHeadLoss (matchingEdges C) N l y at price
  dsimp only [fixedHeadLoss] at price
  have slot (h:ℕ) (three:3≤h) : min (matchingEdges C) (N/(h+1))≤N/4 :=
    (Nat.min_le_right _ _).trans (Nat.div_le_div_left (by omega) (by decide))
  have safe (h:ℕ) (four:4≤h) : min (matchingEdges C) (N/(h+1))≤l :=
    (Nat.min_le_right _ _).trans (Nat.div_le_div_left (by omega) (by decide))
  have a := slot x heads.1
  have b := slot y heads.2.1
  have lo : l≤N/4 := Nat.div_le_div_left (by decide : 4≤5) (by decide)
  refine ⟨w,actual,bound,?_,fun xx yy => ?_⟩
  · rcases heads.2.2 with xx|yy
    · have := safe x xx;omega
    · have := safe y yy;omega
  · have := safe x xx;have := safe y yy;omega

#print axioms fixed_winner_typed_after_prefix
#print axioms third_gap_fixed_head_bounds
end JSP452Audit.StarHost
