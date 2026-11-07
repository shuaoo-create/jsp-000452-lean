import CubicLabelledPairs
namespace JSP452Audit.StarHost
open SimpleGraph
namespace CubicPairFamily
variable {X I : Type*} [Fintype X] [Fintype I] (P : CubicPairFamily X I)

noncomputable def residualCost (G:SimpleGraph X) (U:Set X) : ℕ :=
  fourLabelSum U (fourWhiteDegree G U)+(P.active U).card

theorem white_degree_removal (G : SimpleGraph X) (U T:Set X) (inside:T⊆U) :
    fourLabelSum U (fourWhiteDegree G U)=fourLabelSum (U\T) (fourWhiteDegree G (U\T))+
      fourLabelSum T (fourWhiteDegree G U)+crossCount G T (U\T) := by
  let R := U\T
  have dis : Disjoint T R := Set.disjoint_sdiff_right
  have whole : T∪R=U := by rw [Set.union_comm];exact Set.sdiff_union_of_subset inside
  have splice := four_sum_union T R dis (fourWhiteDegree G U)
  rw [whole] at splice
  have part : fourWhiteDegree G U=(fun x => fourWhiteDegree G T x+fourWhiteDegree G R x) := by
    funext x;rw [←four_degree_split G T R dis,whole]
  have changeR : fourLabelSum R (fourWhiteDegree G U)=crossCount G T R+fourLabelSum R (fourWhiteDegree G R) := by
    rw [part,four_sum_add,four_sum_cross,crossCount_swap]
  rw [changeR] at splice
  change _=fourLabelSum R (fourWhiteDegree G R)+fourLabelSum T (fourWhiteDegree G U)+crossCount G T R
  omega

/-- Removing T costs at most three per removed vertex plus its white edges
to the remainder. Each labelled pair fully inside T gives one extra unit. -/
theorem residual_cost_removal (G : SimpleGraph X) (U T:Set X) (inside:T⊆U)
    (cap : ∀x∈T,fourWhiteDegree G U x+P.degree U x≤3) :
    P.residualCost G U+(P.active T).card≤P.residualCost G (U\T)+3*T.ncard+crossCount G T (U\T) := by
  have split := white_degree_removal G U T inside
  have pairs := P.degree_removal U T inside
  have limited := four_sum_mono T _ _ cap
  rw [four_sum_add,four_sum_const,Nat.mul_comm T.ncard 3] at limited
  unfold residualCost
  omega

/-- A detached four-cycle with no auxiliary pair to the remaining graph
can be covered by two ordinary adjacent pairs. Its total removal cost is
at most ten units even when its internal auxiliary pairs are parallel. -/
theorem isolated_four_cost (G : SimpleGraph X) (U T:Set X) (inside:T⊆U) (size:T.ncard=4)
    (deg : ∀x∈T,fourWhiteDegree G U x=2) (closed : crossCount G T (U\T)=0)
    (pairClosed : (P.active U).card=(P.active (U\T)).card+(P.active T).card)
    (cap : ∀x∈T,fourWhiteDegree G U x+P.degree U x≤3) :
    P.residualCost G U≤P.residualCost G (U\T)+10 := by
  have weight : fourLabelSum T (fourWhiteDegree G U)=8 := by
    have lower := four_sum_mono T _ _ (fun x hx => (deg x hx).ge)
    have upper := four_sum_mono T _ _ (fun x hx => (deg x hx).le)
    rw [four_sum_const,size] at lower upper;omega
  have pairs := P.degree_removal U T inside
  have limited := four_sum_mono T _ _ cap
  rw [four_sum_add,four_sum_const,size,weight] at limited
  have split := white_degree_removal G U T inside
  rw [weight,closed] at split
  unfold residualCost
  omega

end CubicPairFamily
#print axioms CubicPairFamily.white_degree_removal
#print axioms CubicPairFamily.residual_cost_removal
#print axioms CubicPairFamily.isolated_four_cost
end JSP452Audit.StarHost
