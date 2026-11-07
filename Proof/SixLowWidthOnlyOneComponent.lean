import TwoOrThreeRealComponentsPay
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_ordered_pair_excluded (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (width:highestWidth F.n F.m F.r≤3)
    (c v:F.G.ConnectedComponent) (ne:c≠v) (cm:c∈oddRegularComponents F.G 6) (vm:v∈oddRegularComponents F.G 6)
    (ord:matchingEdges c.toSimpleGraph≤matchingEdges v.toSimpleGraph) : False := by
  classical
  let a := matchingEdges c.toSimpleGraph
  let b := matchingEdges v.toSimpleGraph
  let z : Fin 2→F.G.ConnectedComponent := ![c,v]
  have inj : Function.Injective z := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all [z]
  let e : Fin 2 ↪ F.G.ConnectedComponent := ⟨z,inj⟩
  have actual (i:Fin 2) : e i∈oddRegularComponents F.G 6 := by fin_cases i;exact cm;exact vm
  have balance := strict_six_single_spare_guard paid six width c cm {v}
    (fun w mem => (Finset.mem_singleton.mp mem) ▸ vm) (by simpa using ne)
  rw [Finset.sum_singleton] at balance
  change b+3*(F.r+2)≤3*a at balance
  let gap := max a (b-a)
  let k := gap-(F.r+1)
  have small : 2*k≤a+b := by dsimp [k,gap,a,b] at *;omega
  have room : gap≤F.r+k+1 := by dsimp [k];omega
  have menu := two_capacity_splits (fun i:Fin 2 => matchingEdges (e i).toSimpleGraph) (F.r+k) ord
    ((Nat.le_max_left a (b-a)).trans room) ((Nat.le_max_right a (b-a)).trans room)
  apply strict_six_small_menu_impossible F paid six e actual (by simp) (by simpa using width) k _ menu
  rw [Fin.sum_univ_two];exact small

theorem strict_six_width_classification (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 6).ncard
    let ρ := minimumExposure F.G 6
    (h=1 ∧ c=1 ∧ ρ≤2) ∨ (h=4 ∧ c=4 ∧ ρ=4) := by
  classical
  intro h c ρ
  obtain ⟨K⟩ := degreeRegion_exists F.G 6
  obtain ⟨lo,head,body,lim,_⟩ := strict_six_four_exposure_entry F paid six K
  change 1≤h at lo
  change h≤c at head
  change c≤ρ at body
  change ρ≤4 at lim
  by_cases low : h≤3
  · have only : c≤1 := by
      by_contra! multiple
      let Z := oddRegularComponents F.G 6
      let _ := Fintype.ofFinite ↥Z
      have fit : Fintype.card (Fin 2)≤Fintype.card ↥Z := by
        rw [Fintype.card_fin,←Nat.card_eq_fintype_card]
        change 2≤c;omega
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le fit
      let a := e 0
      let b := e 1
      have ne : a.val≠b.val := fun eq => (show (0:Fin 2)≠1 by decide) (e.injective (Subtype.ext eq))
      rcases le_total (matchingEdges a.val.toSimpleGraph) (matchingEdges b.val.toSimpleGraph) with ord|ord
      · exact strict_six_ordered_pair_excluded F paid six low _ _ ne a.property b.property ord
      · exact strict_six_ordered_pair_excluded F paid six low _ _ ne.symm b.property a.property ord
    have eq : c=1 := by omega
    exact Or.inl ⟨by omega,eq,(strict_six_component_exposure_classes F paid six).1 eq⟩
  · exact Or.inr ⟨by omega,by omega,by omega⟩

#print axioms strict_six_ordered_pair_excluded
#print axioms strict_six_width_classification
end JSP452Audit.StarHost
