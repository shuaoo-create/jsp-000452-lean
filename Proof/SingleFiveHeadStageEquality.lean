import OneExteriorAllAxisEdgeCount
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_actual_five_head (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) :
    0<originalThresholdCount F.n 5 ∨ 0<originalThresholdCount F.m 5 := by
  by_contra! none
  apply strict_six_no_five_impossible F paid six
  · intro i;by_contra! high
    have p := (original_threshold_prefix F.n F.hn 5 i).mp high;omega
  · intro i;by_contra! high
    have p := (original_threshold_prefix F.m F.hm 5 i).mp high;omega

theorem single_five_head_shadow_exact (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (c:F.G.ConnectedComponent) (member:c∈oddRegularComponents F.G 6)
    (B:Set ↥(c.suppᶜ:Set F.X)) (stage:CompleteDegreeStage (F.G.induce c.suppᶜ) 6 B) :
    widthAt F.n F.m F.r 6=matchingEdges c.toSimpleGraph+B.ncard+3 := by
  classical
  let e : Fin 1 ↪ F.G.ConnectedComponent := ⟨fun _ => c,fun _ _ _ => Subsingleton.elim _ _⟩
  let T := Finset.univ.map e
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  let P := matchingEdges c.toSimpleGraph
  let k := P-(F.r+1)
  let L := widthAt F.n F.m F.r 6
  have singleton : T={c} := by ext w;simp [T,e];rfl
  have sameU : U=c.supp := by ext x;change F.G.connectedComponentMk x∈T ↔ _;rw [singleton];exact Finset.mem_singleton
  suffices core : ∀B:Set ↥(Uᶜ:Set F.X),CompleteDegreeStage O 6 B → L=P+B.ncard+3 by
    dsimp only [O] at core
    rw [sameU] at core
    exact core B stage
  intro B s6
  have actual (w) (mem:w∈T) : w∈oddRegularComponents F.G 6 := by rw [singleton,Finset.mem_singleton] at mem;exact mem ▸ member
  have card : T.card=1 := by rw [singleton,Finset.card_singleton]
  have rank : matchingEdges (F.G.induce U)=P := by rw [sameU];rfl
  obtain ⟨A,s5⟩ := complete_degree_stage_exists (O.induce Bᶜ) 5
  obtain ⟨J,s4⟩ := complete_degree_stage_exists (O.induce (nestedRemoved B A)ᶜ) 4
  let H : SixFiveFourHistory O := ⟨B,s6,A,s5,J,s4⟩
  have h := (strict_six_only_one_original_component F paid six).1
  have upper := strict_six_short_shadow F paid six T actual B s6
  rw [card,h] at upper
  change L+1≤matchingEdges (F.G.induce U)+B.ncard+(2*1+10)/3 at upper
  rw [rank] at upper
  apply Nat.le_antisymm (by omega)
  by_cases enough : k≤H.fiveCut.ncard
  · have fit : k≤H.fourCut.ncard := by have := H.cut_counts.2;omega
    have menu := split_capacities_of_small (fun i:Fin 1 => matchingEdges (e i).toSimpleGraph) (F.r+k)
      (fun i => by change P≤F.r+k+1;dsimp [k];omega)
    obtain ⟨p5,p6⟩ := strict_six_menu_history_price F paid six e (fun _ => member) k menu H fit
    rw [Fin.sum_univ_one,Fintype.card_fin,h] at p5
    rw [Fintype.card_fin,h] at p6
    change P+3*1+1+min k H.fiveCut.ncard+min k B.ncard≤k+L+1 at p5
    change 3*1+1+min k H.fiveCut.ncard+min k B.ncard≤2*k+1 at p6
    rw [min_eq_left enough] at p5 p6
    omega
  · have small : H.fiveCut.ncard<matchingEdges (F.G.induce U)-(F.r+1) := by rw [rank];change H.fiveCut.ncard<k;omega
    have axis := short_five_cut_has_only_unit_axes F paid six (strict_six_actual_five_head F paid six) T actual card H small
    have low := pure_axes_pay_last_sixth_width F paid six T actual card B s6 axis
    change matchingEdges (F.G.induce U)+B.ncard+3≤L at low
    rwa [rank] at low

#print axioms strict_six_actual_five_head
#print axioms single_five_head_shadow_exact
end JSP452Audit.StarHost
