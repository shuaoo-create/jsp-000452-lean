import TwoSinglePortNineNearPerfectComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure NinePortRegion {X:Type u} [Finite X] (G:SimpleGraph X) where
  K : NineOriginalCut G
  select : Fin 2↪↥K.onePortBlocks
  port : ∀i,K.Port (select i).val
  root_gap : K.S.ncard=K.T.ncard+1
  exposure : 1≤K.eta
  root_count : 1≤(Set.range (fun i => (port i).root)).ncard ∧ (Set.range (fun i => (port i).root)).ncard≤2
  debt : (rootShortfall G (Set.range (fun i => (port i).root)) 9:ℤ)+
    2*((G.induce (Set.range (fun i => (port i).root))).edgeSet.ncard:ℤ)+K.eta≤6
  inner : ∀i,let U := K.labels (select i).val
    U.ncard=2*matchingEdges (G.induce U)+1 ∧ 5≤matchingEdges (G.induce U)

theorem strict_nine_port_region_exists (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) :
    ∃R:NinePortRegion F.G,(highestWidth F.n F.m F.r:ℤ)≤R.K.eta ∧
      ∃M:F.G.Subgraph,M.IsMatching ∧ M.edgeSet.ncard=matchingEdges F.G ∧
      (exposedFull F.G M 9).ncard=minimumExposure F.G 9 ∧
      ∀i,let U := R.K.labels (R.select i).val
        (M.spanningCoe.induce U).edgeSet.ncard=matchingEdges (F.G.induce U) := by
  obtain ⟨K,M,hm,max,opt,width,gap,_,_,e,port,_,lo,hi,debt,inside⟩ :=
    strict_nine_two_ports_share_one_optimal_matching F paid nine
  have hp := (strict_nine_original_peak F paid nine).1
  let R : NinePortRegion F.G := ⟨K,e,port,gap,by omega,⟨lo,hi⟩,debt,fun i => ⟨(inside i).1,(inside i).2.1⟩⟩
  exact ⟨R,width,M,hm,max,opt,fun i => (inside i).2.2⟩

namespace NinePortRegion
variable {X:Type u} [Finite X] {G:SimpleGraph X} (R:NinePortRegion G)
abbrev roots := Set.range (fun i => (R.port i).root)
abbrev box (i:Fin 2) := R.K.labels (R.select i).val
abbrev chosen := R.box 0∪R.box 1
abbrev outside := (R.roots∪R.chosen)ᶜ
noncomputable abbrev capacity (i:Fin 2) := matchingEdges (G.induce (R.box i))
noncomputable abbrev totalCapacity := R.capacity 0+R.capacity 1
noncomputable abbrev outsideRank := matchingEdges (G.induce R.outside)

theorem roots_on_source : R.roots⊆R.K.S := by rintro _ ⟨i,rfl⟩;exact (R.port i).root_mem

theorem disjoint_boxes : Disjoint (R.box 0) (R.box 1) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨v,hv,rfl⟩ ⟨w,hw,eq⟩
  have same : w=v := Subtype.ext eq
  subst w
  have label := (show (G.induce R.K.barrierᶜ).connectedComponentMk v=(R.select 0).val.val from hv).symm.trans hw
  have clash : (0:Fin 2)=1 := R.select.injective (Subtype.ext (Subtype.ext label))
  exact (by decide : (0:Fin 2)≠1) clash

theorem chosen_away : Disjoint R.roots R.chosen := by
  apply Set.disjoint_left.mpr
  intro x root box
  have inCut : x∈R.K.barrier := Or.inl (R.roots_on_source root)
  rcases box with zero|one
  · exact cut_piece_outside G R.K.barrier (R.select 0).val.val zero inCut
  · exact cut_piece_outside G R.K.barrier (R.select 1).val.val one inCut

theorem box_separation (i:Fin 2) {x y:X} (inside:x∈R.box i) (e:G.Adj x y) :
    y∈R.box i ∨ y=(R.port i).root := by
  by_cases present:y∈R.box i
  · exact Or.inl present
  · exact Or.inr ((R.port i).only x inside y present e).2

theorem chosen_structure :
    R.chosen.ncard=2*R.totalCapacity+2 ∧
    Nonempty (((G.induce (R.box 0))⊕g (G.induce (R.box 1))) ≃g G.induce R.chosen) := by
  have count := Set.ncard_union_eq R.disjoint_boxes
  change R.chosen.ncard=(R.box 0).ncard+(R.box 1).ncard at count
  have zero := (R.inner 0).1
  have one := (R.inner 1).1
  change (R.box 0).ncard=2*R.capacity 0+1 at zero
  change (R.box 1).ncard=2*R.capacity 1+1 at one
  refine ⟨by change R.chosen.ncard=2*(R.capacity 0+R.capacity 1)+2;omega,?_⟩
  exact ⟨regionSumIso G R.chosen (R.box 0) (R.box 1) rfl R.disjoint_boxes (fun x hx y hy adj =>
    (R.box_separation 0 hx adj).elim (fun h => Set.disjoint_left.mp R.disjoint_boxes h hy)
      (fun h => Set.disjoint_left.mp R.chosen_away ⟨0,h.symm⟩ (Or.inr hy)))⟩

#print axioms roots_on_source
#print axioms disjoint_boxes
#print axioms chosen_away
#print axioms box_separation
#print axioms chosen_structure
end NinePortRegion
#print axioms strict_nine_port_region_exists
end JSP452Audit.StarHost
