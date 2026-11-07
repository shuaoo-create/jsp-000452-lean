import ReturnEveryPaidRectangleToTheActualInducedExterior
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph JSP452Audit.Padded
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} {K:TenBlockPartition G} {q:ℕ} (R:TenPortSupport G K q)

abbrev coverBlue (S : Set X) := portInside R.piece Sᶜ
abbrev coverRed (S : Set X) := R.piece \ R.coverBlue S

theorem chosen_internal_edge {x y : X} (hx : x∈R.support) (hy : y∈R.support) (e : G.Adj x y) :
    R.piece.Adj x y := by
  exact ⟨e,fun both => both.1 hx⟩

theorem cover_red_rank (S : Set X) : matchingEdges (R.coverRed S)≤S.ncard := by
  apply matchingEdges_le_cover_card
  intro x y edge
  by_cases ins : x∈S
  · exact Or.inl ins
  · by_cases yin : y∈S
    · exact Or.inr yin
    · exact (edge.2 ((portInside_adj R.piece Sᶜ x y).mpr ⟨edge.1,ins,yin⟩)).elim

theorem cover_palette_spans (S : Set X) : G≤((G \ R.piece)⊔R.coverRed S)⊔R.coverBlue S := by
  intro x y e
  by_cases ins : R.piece.Adj x y
  · by_cases blue : (R.coverBlue S).Adj x y
    · exact Or.inr blue
    · exact Or.inl (Or.inr ⟨ins,blue⟩)
  · exact Or.inl (Or.inl ⟨e,ins⟩)

theorem point_cover_blue_vertices {I : Type*} [Finite I] (S : Set X) (tips : R.innerTips⊆S)
    (inside : S⊆R.support) (A : SimpleGraph X) (sub : A≤(G \ R.piece)) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy (A⊔R.coverBlue S))
    (i : I) (hit : i∈touchedStars A (R.coverBlue S) (fun _ : I => a) f) :
    f (center (fun _ : I => a) i)∈R.support\S ∧
      ∀j : Fin (a+1),f ⟨i,j⟩∈(R.support\S) := by
  let n := fun _ : I => a
  obtain ⟨k,miss⟩ := hit
  have mark := (f.toHom.map_adj (starEdge n ⟨i,k⟩)).resolve_left miss
  obtain ⟨edge,xc,yc⟩ := (portInside_adj R.piece Sᶜ _ _).mp mark
  have chosen := (R.ordinary_center_or_marked_leaf edge).resolve_right (fun h => yc (tips h))
  have atCenter : f (center n i)∈R.support\S := ⟨chosen,xc⟩
  refine ⟨atCenter,fun j => Fin.cases atCenter (fun l => ?_) j⟩
  let x := f (center n i)
  let y := f (leaf n ⟨i,l⟩)
  have adj : (A⊔R.coverBlue S).Adj x y := f.toHom.map_adj (starEdge n ⟨i,l⟩)
  have original : G.Adj x y := adj.elim (fun h => (sub h).1) (fun h => (eraseInternal_le G _) ((portInside_adj _ _ x y).mp h).1)
  have whereY := R.ordinary_neighbors_stay chosen (fun h => xc (tips h)) original
  have free : y∉S := by
    intro mem
    rcases adj with kept|blue
    · exact (sub kept).2 (R.chosen_internal_edge chosen (inside mem) original)
    · exact ((portInside_adj _ _ x y).mp blue).2.2 mem
  exact ⟨whereY,free⟩

theorem cover_blue_damage {I : Type*} [Finite I] (S : Set X) (tips : R.innerTips⊆S) (inside : S⊆R.support)
    (A : SimpleGraph X) (sub : A≤(G \ R.piece)) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy (A⊔R.coverBlue S)) :
    let T := touchedStars A (R.coverBlue S) (fun _ : I => a) f
    (a+1)*T.ncard+S.ncard≤R.support.ncard ∧
      (S.ncard=R.support.ncard → T.ncard=0) := by
  intro T
  let V := (R.support\S)
  have use (i) (mem : i∈T) := R.point_cover_blue_vertices S tips inside A sub a f i mem
  have pack := (packed_star_classes _ a f T ∅ (by simp) V ∅
    (fun i h => (use i h).2) (fun _ h => h.elim) (Set.empty_subset _)).2
  simp only [Set.ncard_empty,Nat.add_zero] at pack
  have split := Set.ncard_sdiff_add_ncard_of_subset inside
  change (a+1)*T.ncard≤(R.support\S).ncard at pack
  refine ⟨by omega,?_⟩
  intro full
  have eq : R.support=S := (Set.eq_of_subset_of_ncard_le inside full.ge).symm
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
end JSP452Audit.StarHost.TenPortSupport
