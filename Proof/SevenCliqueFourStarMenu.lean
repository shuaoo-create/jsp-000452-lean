import FixedExteriorForestSubstitution
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
namespace JSP452Audit.StarHost
open SimpleGraph

def sevenStarLeaves : Fin 4→ℕ := ![7,6,6,1]

def fourCount (f:Fin 4→ℕ) (x:ℕ) : ℕ :=
  (if x≤f 0 then 1 else 0)+(if x≤f 1 then 1 else 0)+
  (if x≤f 2 then 1 else 0)+(if x≤f 3 then 1 else 0)

def fitsThree (f:Fin 4→ℕ) (a b c:ℕ) : Prop :=
  1≤fourCount f a ∧ 2≤fourCount f b ∧ 3≤fourCount f c

instance (f:Fin 4→ℕ) (a b c:ℕ) : Decidable (fitsThree f a b c) := by
  unfold fitsThree
  infer_instance

def fourStarMenu (f g:Fin 4→ℕ) : Prop :=
  fitsThree f 5 2 1 ∨ fitsThree g 5 2 1 ∨
  (fitsThree f 4 1 0 ∧ fitsThree g 5 2 0) ∨ (fitsThree g 4 1 0 ∧ fitsThree f 5 2 0) ∨
  (fitsThree f 4 2 1 ∧ fitsThree g 2 2 1) ∨ (fitsThree g 4 2 1 ∧ fitsThree f 2 2 1)

instance (f g:Fin 4→ℕ) : Decidable (fourStarMenu f g) := by
  unfold fourStarMenu
  infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
theorem four_star_split_table (a:Fin 8) (b c:Fin 7) (e:Fin 2) :
    fourStarMenu ![a.val,b.val,c.val,e.val] ![7-a.val,6-b.val,6-c.val,1-e.val] := by
  revert b c e
  fin_cases a <;> decide +kernel

theorem four_star_actual_menu (R : SimpleGraph (Vertices sevenStarLeaves)) :
    fourStarMenu (fun i => Nat.card (Colored sevenStarLeaves R i))
      (fun i => Nat.card (Colored sevenStarLeaves ((forest sevenStarLeaves) \ R) i)) := by
  let f := fun i => Nat.card (Colored sevenStarLeaves R i)
  let g := fun i => Nat.card (Colored sevenStarLeaves ((forest sevenStarLeaves) \ R) i)
  have part (i:Fin 4) : f i+g i=sevenStarLeaves i := colors_partition sevenStarLeaves R i
  have a : f 0+g 0=7 := part 0
  have b : f 1+g 1=6 := part 1
  have c : f 2+g 2=6 := part 2
  have e : f 3+g 3=1 := part 3
  have raw := four_star_split_table ⟨f 0,by omega⟩ ⟨f 1,by omega⟩ ⟨f 2,by omega⟩ ⟨f 3,by omega⟩
  have feq : f=![f 0,f 1,f 2,f 3] := by funext i;fin_cases i <;> rfl
  have geq : g=![7-f 0,6-f 1,6-f 2,1-f 3] := by
    funext i;fin_cases i <;> simp <;> omega
  change fourStarMenu f g
  rw [feq,geq]
  exact raw

theorem four_star_edge_price : (forest sevenStarLeaves).edgeSet.ncard=20 := by
  rw [←Nat.card_coe_set_eq,edge_count]
  decide +kernel

#print axioms four_star_split_table
#print axioms four_star_actual_menu
#print axioms four_star_edge_price
end JSP452Audit.StarHost
