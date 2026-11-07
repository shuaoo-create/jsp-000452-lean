import ThreeWholeComponentGap
import Mathlib.Data.Fin.Tuple.Sort
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_four_components_excluded (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (card:(oddRegularComponents F.G 6).ncard=4) : False := by
  classical
  let Z := oddRegularComponents F.G 6
  let _ := Fintype.ofFinite ↥Z
  have enough : Fintype.card (Fin 4)≤Fintype.card ↥Z := by
    rw [Fintype.card_fin,←Nat.card_eq_fintype_card];change 4≤(oddRegularComponents F.G 6).ncard;omega
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le enough
  let val (i:Fin 4) := matchingEdges (pick i).val.toSimpleGraph
  let labels : Fin 4 ↪ F.G.ConnectedComponent :=
    ((Tuple.sort val).toEmbedding.trans pick).trans (Function.Embedding.subtype (·∈Z))
  let z (i:Fin 4) := matchingEdges (labels i).toSimpleGraph
  have sorted : Monotone z := Tuple.monotone_sort val
  have real (i:Fin 4) : labels i∈Z := (pick (Tuple.sort val i)).property
  let a := z 0
  let b := z 1
  let c := z 2
  let d := z 3
  have ab : a≤b := sorted (by decide : (0:Fin 4)≤1)
  have bc : b≤c := sorted (by decide : (1:Fin 4)≤2)
  have cd : c≤d := sorted (by decide : (2:Fin 4)≤3)
  let pair := (Fin.castLEEmb (by decide : 2≤4)).trans labels
  let S : Finset F.G.ConnectedComponent := {labels 2,labels 3}
  have remaining (v) (mem:v∈S) : v∈Z := by
    rcases Finset.mem_insert.mp mem with eq|eq
    · exact eq ▸ real 2
    · exact (Finset.mem_singleton.mp eq) ▸ real 3
  have outside (i:Fin 2) : pair i∉S := by
    have n2 : labels ((Fin.castLEEmb (by decide : 2≤4)) i)≠labels 2 := by
      intro eq;have := congrArg Fin.val (labels.injective eq);change i.val=2 at this;omega
    have n3 : labels ((Fin.castLEEmb (by decide : 2≤4)) i)≠labels 3 := by
      intro eq;have := congrArg Fin.val (labels.injective eq);change i.val=3 at this;omega
    intro mem
    rcases Finset.mem_insert.mp mem with eq|eq
    · exact n2 eq
    · exact n3 (Finset.mem_singleton.mp eq)
  have guard := strict_six_two_spare_guard paid six pair (fun i => real _) S remaining outside ab
  have diff : labels 2≠labels 3 := fun eq => (by decide : (2:Fin 4)≠3) (labels.injective eq)
  change (∑v∈({labels 2,labels 3}:Finset _),matchingEdges v.toSimpleGraph)+3*(F.r+2)≤3*max a (b-a) at guard
  rw [Finset.sum_pair diff] at guard
  change c+d+3*(F.r+2)≤3*max a (b-a) at guard
  let ix : Fin 3→Fin 4 := ![2,0,1]
  have ixInj : Function.Injective ix := by intro i j eq;fin_cases i <;> fin_cases j <;> simp_all [ix]
  let triple : Fin 3 ↪ F.G.ConnectedComponent := (⟨ix,ixInj⟩ : Fin 3 ↪ Fin 4).trans labels
  let g := max (max a (b-a)) (c-(a+b))
  let k := g-(F.r+1)
  have gap : 2*g≤a+b+c := by dsimp [g];omega
  have reach : g≤F.r+k+1 := by dsimp [k];omega
  have menu := three_capacity_splits (fun i:Fin 3 => matchingEdges (triple i).toSimpleGraph) (F.r+k) ab
    (show a≤F.r+k+1 by dsimp [g] at reach;omega)
    (show b-a≤F.r+k+1 by dsimp [g] at reach;omega)
    (show c-(a+b)≤F.r+k+1 by dsimp [g] at reach;omega)
  have width := (strict_six_real_component_bounds F paid six).2.1.trans_eq card
  apply strict_six_small_menu_impossible F paid six triple (fun i => real _) (by simp) (by simpa using width) k _ menu
  rw [Fin.sum_univ_three]
  change 2*k≤c+a+b
  dsimp [k];omega

theorem strict_six_only_one_original_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) :
    highestWidth F.n F.m F.r=1 ∧ (oddRegularComponents F.G 6).ncard=1 ∧ minimumExposure F.G 6≤2 := by
  rcases strict_six_width_classification F paid six with last|four
  · exact last
  · exact (strict_six_four_components_excluded F paid six four.2.1).elim

#print axioms strict_six_four_components_excluded
#print axioms strict_six_only_one_original_component
end JSP452Audit.StarHost
