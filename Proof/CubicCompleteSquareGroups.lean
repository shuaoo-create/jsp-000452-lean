import CubicIsolatedAndAttachedSquare
namespace JSP452Audit.StarHost.CubicPairFamily
open SimpleGraph
variable {X I : Type*} [Fintype X] [Fintype I] (P:CubicPairFamily X I)

/-- Two different four-cycle components joined by a real blue pair:
select its centre and repair the remaining three vertices of each square. -/
theorem square_to_square (G:SimpleGraph X) (U:Set X) (c d:(G.induce U).ConnectedComponent) (ne:c≠d)
    (left:CubicSquareSite G U c) (right:CubicSquareSite G U d)
    (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3) (p u w:X) (pc:p∈cubicWhiteSite G U c)
    (ud:u∈cubicWhiteSite G U d) (pw:G.Adj p w) (uw:G.Adj u w) : P.PaidRemoval G U := by
  let T := cubicWhiteSite G U c
  let Y := cubicWhiteSite G U d
  let W := T∪Y
  have sub : W⊆U := Set.union_subset (site_in_white G U c) (site_in_white G U d)
  have n : W.ncard=8 := by dsimp [W];rw [Set.ncard_union_eq (sites_disjoint G U c d ne),left.size,right.size]
  have cross : crossCount G W (U\W)=0 := crossCount_of_no_edges G W (U\W) (fun _ hx _ hy e => by
    rcases hx with tc|yc
    · exact hy.2 (Or.inl (site_closed_adj G U c tc hy.1 e))
    · exact hy.2 (Or.inr (site_closed_adj G U d yc hy.1 e)))
  obtain ⟨a,_,first⟩ := left.repair p pc
  obtain ⟨b,_,second⟩ := right.repair u ud
  let S : Set X := insert w ({a,b} : Set X)
  have count : S.ncard≤3 := by
    have two := Set.ncard_insert_le a ({b}:Set X)
    rw [Set.ncard_singleton] at two
    have three := Set.ncard_insert_le w ({a,b}:Set X);dsimp [S];omega
  apply P.removal_of_cross_price G U W S sub ⟨p,Or.inl pc⟩ _ cap _
  · intro x hx
    rcases hx with fromT|fromY
    · by_cases same:x=p
      · exact Or.inr ⟨w,Set.mem_insert _ _,same.symm ▸ pw⟩
      rcases first x fromT same with eq|edge
      · exact Or.inl (Or.inr (Or.inl eq))
      · exact Or.inr ⟨a,Or.inr (Or.inl rfl),edge⟩
    · by_cases same:x=u
      · exact Or.inr ⟨w,Set.mem_insert _ _,same.symm ▸ uw⟩
      rcases second x fromY same with eq|edge
      · exact Or.inl (Or.inr (Or.inr eq))
      · exact Or.inr ⟨b,Or.inr (Or.inr rfl),edge⟩
  · omega

/-- Every remaining white set which has an ordinary degree-two vertex has
an actual removable group. All white components and auxiliary edges used
here are those of the given U. -/
theorem paid_step_at_degree_two (G:SimpleGraph X) (U:Set X) (v:U) (full:2≤fourWhiteDegree G U v.val)
    (degree:∀x∈U,fourWhiteDegree G U x≤2) (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3)
    (centers:∀j∈P.active U,∃w:X,G.Adj (P.left j) w ∧ G.Adj (P.right j) w) : P.PaidRemoval G U := by
  classical
  let c := (G.induce U).connectedComponentMk v
  let T := cubicWhiteSite G U c
  rcases P.paid_or_square_at_degree_two G U v full degree cap with paid|square
  · exact paid
  by_cases closed : ∀j∈P.active U,P.left j∈T ↔ P.right j∈T
  · exact P.square_without_outgoing_pair G U c square cap closed
  push Not at closed
  obtain ⟨j,mem,diff⟩ := closed
  obtain ⟨w,lw,rw'⟩ := centers j mem
  obtain ⟨lU,rU⟩ := (P.mem_active U j).1 mem
  have connect (p u:X) (pT:p∈T) (uU:u∈U) (outside:u∉T) (pw:G.Adj p w) (uw:G.Adj u w)
      (pair:j∈P.active (insert u T)) : P.PaidRemoval G U := by
    by_cases low : fourWhiteDegree G U u≤1
    · exact P.square_to_low_vertex G U c square cap p u w pT uU outside low pw uw (Finset.card_pos.mpr ⟨j,pair⟩)
    let y : U := ⟨u,uU⟩
    let d := (G.induce U).connectedComponentMk y
    have yD : u∈cubicWhiteSite G U d := ⟨y,rfl,rfl⟩
    rcases P.paid_or_square_at_degree_two G U y (by change 2≤fourWhiteDegree G U u;omega) degree cap with yes|right
    · exact yes
    have ne : c≠d := fun eq => outside (by change u∈cubicWhiteSite G U c;rw [eq];exact yD)
    exact P.square_to_square G U c d ne square right cap p u w pT yD pw uw
  rcases diff with ⟨left,right⟩|⟨left,right⟩
  · exact connect _ _ left rU right lw rw' ((P.mem_active _ j).2 ⟨Or.inr left,Or.inl rfl⟩)
  · exact connect _ _ right lU left rw' lw ((P.mem_active _ j).2 ⟨Or.inl rfl,Or.inr right⟩)

#print axioms square_to_square
#print axioms paid_step_at_degree_two
end JSP452Audit.StarHost.CubicPairFamily
