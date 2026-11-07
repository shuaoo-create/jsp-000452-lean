import SharpPointCoverOrMonochromeTaxForEveryOriginalHeightPair
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def actualCoordinateLoss (Z N r x y:ℕ) := if x=1 ∨ y=1 then Z else pointCoordinateTax Z N r x y

theorem typed_inventory_on_actual_cut {X:Type*} [Finite X] (Y:SimpleGraph X) {a b w j:ℕ}
    (pa:0<a) (pb:0<b) (height:a+b-1=j+1) (positive:0<j) (actual:ExactTypedWidth Y a b w)
    (T:Set X) (low:∀v:↥(Tᶜ:Set X),Nat.card ((Y.induce Tᶜ).neighborSet v)<j) : w≤T.ncard := by
  rcases actual with dead|⟨u,v,hu,hv,num,force⟩
  · omega
  have bound := uniform_le_deletion Y a b u v j pa pb hu hv positive height force
  have witness : admits_matching_remainder (Y.induce Tᶜ) j := by
    refine ⟨⊥,fun _ h => h.elim,?_⟩
    intro z
    rw [Subgraph.spanningCoe_bot,sdiff_bot]
    have := low z;omega
  exact num ▸ bound.trans (deletionBudget_le_of_witness Y j T witness)

theorem strict_exterior_typed_column_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    {j x y:ℕ} (win:WinsHeight F.n F.m (F.r+P.cutRoots.ncard) j x y) :
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let J := actualCoordinateLoss P.capacity P.paidCore.ncard r x y
    let w := widthAt F.n F.m r j-J
    ExactTypedWidth Y x y w ∧ w≤uniformEnvelope Y j ∧
      ∀T:Set ↥P.exterior,ExactTypedWidth (Y.induce Tᶜ) x y (w-T.ncard) ∧
        (1<j → (∀v:↥(Tᶜ:Set ↥P.exterior),Nat.card ((Y.induce Tᶜ).neighborSet v)<j-1) → w≤T.ncard) := by
  intro r Y J w
  obtain ⟨px,py,eq,rf,bg,win⟩ := win
  obtain ⟨long,_,_,_,_,row⟩ := strict_payable_exterior_constraints F paid P
  have len : P.capacity<min F.s F.t := by omega
  have size : Nat.card ↥P.paidCore=P.paidCore.ncard := Nat.card_coe_set_eq _
  have actual : ExactTypedWidth Y x y w := by
    dsimp only [w,J,actualCoordinateLoss]
    rw [win]
    split_ifs with unit
    · exact unit_summand_coordinate Y _ F.n F.m F.hn F.hm F.pn F.pm len px py rf bg unit row
    · rw [←size]
      exact sharp_summand_coordinate Y _ F.n F.m F.hn F.hm px py rf bg row
  have env : w≤uniformEnvelope Y j := by
    rcases actual with zero|⟨u,v,hu,hv,num,force⟩
    · omega
    · exact num ▸ uniform_pair_le_envelope Y x y u v j px py hu hv eq force
  exact ⟨actual,env,fun T => ⟨typed_width_after_deletion Y T px py actual,fun hj cap =>
    typed_inventory_on_actual_cut Y px py (by omega : x+y-1=(j-1)+1) (by omega) actual T cap⟩⟩

#print axioms typed_inventory_on_actual_cut
#print axioms strict_exterior_typed_column_inventory
end JSP452Audit.StarHost
