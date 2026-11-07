import NinthColumnAndExactErasureReserve
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph JSP452Audit.Padded
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

abbrev coverBlue (S : Set X) := portInside R.adapted Sᶜ
abbrev coverRed (S : Set X) := R.adapted \ R.coverBlue S

theorem chosen_internal_edge {x y : X} (hx : x∈R.chosen) (hy : y∈R.chosen) (e : G.Adj x y) :
    R.adapted.Adj x y := by
  have side (i : Fin 2) (ins : x∈R.box i) : (R.portPart i).Adj x y := by
    have box := (R.box_separation i ins e).resolve_right (fun eq =>
      Set.disjoint_left.mp R.chosen_away (show y∈R.roots from ⟨i,eq.symm⟩) hy)
    exact R.internal_in_portPart i ((portInside_adj G (R.box i) x y).mpr ⟨e,ins,box⟩)
  exact hx.elim (fun h => Or.inl (side 0 h)) (fun h => Or.inr (side 1 h))

theorem cover_red_rank (S : Set X) : matchingEdges (R.coverRed S)≤S.ncard := by
  apply matchingEdges_le_cover_card
  intro x y edge
  by_cases ins : x∈S
  · exact Or.inl ins
  · by_cases yin : y∈S
    · exact Or.inr yin
    · exact (edge.2 ((portInside_adj R.adapted Sᶜ x y).mpr ⟨edge.1,ins,yin⟩)).elim

theorem cover_palette_spans (S : Set X) : G≤(R.erased⊔R.coverRed S)⊔R.coverBlue S := by
  intro x y e
  by_cases ins : R.adapted.Adj x y
  · by_cases blue : (R.coverBlue S).Adj x y
    · exact Or.inr blue
    · exact Or.inl (Or.inr ⟨ins,blue⟩)
  · exact Or.inl (Or.inl ⟨e,ins⟩)

theorem point_cover_blue_vertices {I : Type*} [Finite I] (S : Set X) (tips : R.paidTips⊆S)
    (inside : S⊆R.chosen) (A : SimpleGraph X) (sub : A≤R.erased) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy (A⊔R.coverBlue S))
    (i : I) (hit : i∈touchedStars A (R.coverBlue S) (fun _ : I => a) f) :
    f (center (fun _ : I => a) i)∈R.chosen\S ∧
      ∀j : Fin (a+1),f ⟨i,j⟩∈(R.chosen\S)∪R.looseRoots := by
  let n := fun _ : I => a
  obtain ⟨k,miss⟩ := hit
  have mark := (f.toHom.map_adj (starEdge n ⟨i,k⟩)).resolve_left miss
  obtain ⟨edge,xc,yc⟩ := (portInside_adj R.adapted Sᶜ _ _).mp mark
  have chosen := (R.adapted_center_or_paid_leaf edge).resolve_right (fun h => yc (tips h))
  have atCenter : f (center n i)∈R.chosen\S := ⟨chosen,xc⟩
  refine ⟨atCenter,fun j => Fin.cases (Or.inl atCenter) (fun l => ?_) j⟩
  let x := f (center n i)
  let y := f (leaf n ⟨i,l⟩)
  have adj : (A⊔R.coverBlue S).Adj x y := f.toHom.map_adj (starEdge n ⟨i,l⟩)
  have original : G.Adj x y := adj.elim (fun h => (sub h).1) (fun h => R.adapted_le ((portInside_adj _ _ x y).mp h).1)
  have whereY := R.neighbor_of_ordinary_center chosen (fun h => xc (tips h)) original
  have free : y∉S := by
    intro mem
    rcases adj with kept|blue
    · exact (sub kept).2 (R.chosen_internal_edge chosen (inside mem) original)
    · exact ((portInside_adj _ _ x y).mp blue).2.2 mem
  exact whereY.elim (fun yy => Or.inl ⟨yy,free⟩) Or.inr

theorem cover_blue_damage {I : Type*} [Finite I] (S : Set X) (tips : R.paidTips⊆S) (inside : S⊆R.chosen)
    (A : SimpleGraph X) (sub : A≤R.erased) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy (A⊔R.coverBlue S)) :
    let T := touchedStars A (R.coverBlue S) (fun _ : I => a) f
    (a+1)*T.ncard+S.ncard+R.portCount≤2*R.totalCapacity+4 ∧
      (S.ncard=R.chosen.ncard → T.ncard=0) := by
  intro T
  let V := (R.chosen\S)∪R.looseRoots
  have use (i) (mem : i∈T) := R.point_cover_blue_vertices S tips inside A sub a f i mem
  have pack := (packed_star_classes _ a f T ∅ (by simp) V ∅
    (fun i h => (use i h).2) (fun _ h => h.elim) (Set.empty_subset _)).2
  simp only [Set.ncard_empty,Nat.add_zero] at pack
  have lim := Set.ncard_union_le (R.chosen\S) R.looseRoots
  change V.ncard≤_ at lim
  have split := Set.ncard_sdiff_add_ncard_of_subset inside
  have roots := R.physical_tip_and_root_counts.2.2
  have order := R.chosen_structure.1
  refine ⟨by omega,?_⟩
  intro full
  have eq : R.chosen=S := (Set.eq_of_subset_of_ncard_le inside full.ge).symm
  have empty : T=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i h
    have u := (use i h).1
    exact u.2 (eq ▸ u.1)
  rw [empty,Set.ncard_empty]

#print axioms chosen_internal_edge
#print axioms cover_red_rank
#print axioms cover_palette_spans
#print axioms point_cover_blue_vertices
#print axioms cover_blue_damage
end JSP452Audit.StarHost.NinePortRegion
