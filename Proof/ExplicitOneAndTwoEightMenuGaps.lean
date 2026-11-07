import EightSevenMenuPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem chosen_eight_gap_dominates_stages {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (eight:diagonal F.n F.m (F.r+2)-1=8)
    (e:I↪F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 8) (g:ℕ)
    (split:SplitCapacities (fun i => Nat.card (e i).supp/2) (F.r+(g-(F.r+1))))
    (entry:(Fintype.card I=1 ∧ highestWidth F.n F.m F.r=1) ∨ (Fintype.card I=2 ∧ highestWidth F.n F.m F.r≤4))
    (B:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (first:CompleteDegreeStage (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ) 8 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ).induce Bᶜ) 7 C) :
    F.r+B.ncard+C.ncard+1<g := by
  have short := regular_eight_menu_must_pass_seven F paid eight e actual (g-(F.r+1)) split entry B first C second
  omega

theorem single_eight_gap_is_half_order (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (e:Fin 1↪F.G.ConnectedComponent)
    (actual:∀i,e i∈oddRegularComponents F.G 8) (one:highestWidth F.n F.m F.r=1)
    (B:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (first:CompleteDegreeStage (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ) 8 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ).induce Bᶜ) 7 C) :
    F.r+B.ncard+C.ncard+1<Nat.card (e 0).supp/2 := by
  apply chosen_eight_gap_dominates_stages F paid eight e actual _ _ (Or.inl ⟨Fintype.card_fin 1,one⟩) B first C second
  apply split_capacities_of_small
  intro i
  rw [Subsingleton.elim i 0];omega

theorem pair_eight_gap_is_actual_spacing (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (e:Fin 2↪F.G.ConnectedComponent)
    (actual:∀i,e i∈oddRegularComponents F.G 8) (width:highestWidth F.n F.m F.r≤4)
    (order:Nat.card (e 0).supp/2≤Nat.card (e 1).supp/2)
    (B:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (first:CompleteDegreeStage (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ) 8 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ).induce Bᶜ) 7 C) :
    let a := Nat.card (e 0).supp/2
    let b := Nat.card (e 1).supp/2
    F.r+B.ncard+C.ncard+1<max a (b-a) := by
  intro a b
  apply chosen_eight_gap_dominates_stages F paid eight e actual _ _ (Or.inr ⟨Fintype.card_fin 2,width⟩) B first C second
  apply two_capacity_splits _ _ order
  · change a≤F.r+(max a (b-a)-(F.r+1))+1;omega
  · change b-a≤F.r+(max a (b-a)-(F.r+1))+1;omega

#print axioms chosen_eight_gap_dominates_stages
#print axioms single_eight_gap_is_half_order
#print axioms pair_eight_gap_is_actual_spacing
end JSP452Audit.StarHost
