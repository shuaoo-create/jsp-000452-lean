import FourAndFiveCyclesOnTheTripartiteHost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem carry_tripartite_palette {X:Type*} (Q:SimpleGraph X) (e:Q ≃g threeByThreeHost) :
    ∃R:SimpleGraph X,R≤Q ∧ UniformPackCap R 2 2 ∧ UniformPackCap (Q \ R) 5 0 := by
  obtain ⟨sub,red,blue⟩ := two_cycle_palette_on_nine
  let R := twoCycleColor.comap e
  have incl : R≤Q := fun _ _ edge => e.map_rel_iff.mp (sub edge)
  let redCopy : R.Copy twoCycleColor := {toHom := {toFun := e,map_rel' := fun a => a},injective' := e.injective}
  let blueCopy : (Q \ R).Copy (threeByThreeHost \ twoCycleColor) := {
    toHom := {toFun := e,map_rel' := fun edge => ⟨e.map_rel_iff.mpr edge.1,edge.2⟩}
    injective' := e.injective }
  exact ⟨R,incl,fun k copy => red k (by obtain ⟨f⟩ := copy;exact ⟨redCopy.comp f⟩),
    fun k copy => blue k (by obtain ⟨f⟩ := copy;exact ⟨blueCopy.comp f⟩)⟩

theorem strict_source_degree_six_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) : False := by
  have count := (strict_six_only_one_original_component F paid six).2.1
  obtain ⟨c,mem⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<(oddRegularComponents F.G 6).ncard by omega)
  obtain ⟨rank,order,_⟩ := strict_last_component_has_nine_vertices F paid six c mem
  have reg (v:c.supp) := (component_degree_eq F.G c v).trans (mem.2 v.val v.property)
  have size (A:Set c.supp) (stage:CompleteDegreeStage c.toSimpleGraph 6 A) : 3≤A.ncard := by
    have need := single_six_stage_minimum_size F paid six c mem A stage;omega
  obtain ⟨e⟩ := physical_nine_vertex_iso c.toSimpleGraph order reg size
  obtain ⟨R,sub,red,blue⟩ := carry_tripartite_palette _ e
  have impossible := strict_last_component_packing_obstruction F paid six c mem R sub 2 red blue
  omega

theorem strict_source_degree_at_least_seven (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    7≤diagonal F.n F.m (F.r+2)-1 := by
  have lo := strict_source_degree_at_least_six F paid
  by_contra! small
  exact strict_source_degree_six_impossible F paid (by omega)

theorem original_failure_needs_degree_seven {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail:sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧ 7≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ OnlyDoubleEscape F := by
  obtain ⟨F,paid,_,edges,order,regime⟩ := original_failure_only_double_escape.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_seven F paid,edges,order,regime⟩

#print axioms carry_tripartite_palette
#print axioms strict_source_degree_six_impossible
#print axioms strict_source_degree_at_least_seven
#print axioms original_failure_needs_degree_seven
end JSP452Audit.StarHost
