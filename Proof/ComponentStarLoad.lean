import TwoAgainstBinary
import ComponentSplitColor
open private JSP452Audit.StarHost.rank_component_sides from ComponentSplitColor
namespace JSP452Audit.StarHost
open SimpleGraph
variable {I X : Type*} [Fintype I] [Finite X]

private def forgetStar (n : I→ℕ) (A : Set I) (w : Vertices (fun i:A => n i.val)) : Vertices n :=
  ⟨w.1.val,w.2⟩

omit [Fintype I] in
private theorem forgetStar_injective (n : I→ℕ) (A : Set I) : Function.Injective (forgetStar n A) := by
  rintro ⟨⟨i,hi⟩,a⟩ ⟨⟨j,hj⟩,b⟩ eq
  have ij : i=j := congrArg Sigma.fst eq
  subst j
  have val := congrArg (fun w : Vertices n => w.2.val) eq
  exact congrArg (Sigma.mk (⟨i,hi⟩ : A)) (Fin.ext val)

private def restrictStarCopy (G : SimpleGraph X) (n : I→ℕ) (f : (forest n).Copy G)
    (A : Set I) (U : Set X) (inside : ∀i∈A,∀j : Fin (n i+1),f ⟨i,j⟩∈U) :
    (forest (fun i:A => n i.val)).Copy (G.induce U) where
  toHom := {
    toFun w := ⟨f (forgetStar n A w),inside w.1.val w.1.property w.2⟩
    map_rel' := by
      intro a b h
      apply f.toHom.map_rel'
      have dif : forgetStar n A a ≠ forgetStar n A b := fun eq => h.1 (forgetStar_injective n A eq)
      rcases h.2 with h|h
      · exact ⟨dif,Or.inl ⟨congrArg Subtype.val h.1,h.2⟩⟩
      · exact ⟨dif,Or.inr ⟨congrArg Subtype.val h.1,h.2⟩⟩ }
  injective' := fun _ _ eq => forgetStar_injective n A (f.injective (congrArg Subtype.val eq))

omit [Fintype I] [Finite X] in
private theorem component_of_star_vertex (G : SimpleGraph X) (n : I→ℕ) (f : (forest n).Copy G)
    (i : I) (j : Fin (n i+1)) :
    G.connectedComponentMk (f (center n i))=G.connectedComponentMk (f ⟨i,j⟩) := by
  refine Fin.cases rfl (fun k => ?_) j
  exact ConnectedComponent.sound ((f.toHom.map_rel' (starEdge n ⟨i,k⟩)).reachable)

/-- At host matching rank every component receives exactly its rank in
stars. The centers determine each star's component; the vertex budget sums
the actual leaves of precisely those stars. -/
theorem star_load_at_matching_rank (G : SimpleGraph X) (n : I→ℕ) (pn : ∀i,1≤n i)
    (f : (forest n).Copy G) (tight : Fintype.card I=matchingEdges G) (c : G.ConnectedComponent) :
    let A := {i | f (center n i) ∈ c.supp}
    A.ncard=matchingEdges c.toSimpleGraph ∧
      (∑ᶠ i : A,(n i.val+1))≤Nat.card c.supp := by
  classical
  intro A
  let T := c.supp
  have inside (i : I) (hi : i∈A) (j : Fin (n i+1)) : f ⟨i,j⟩∈T :=
    (component_of_star_vertex G n f i j).symm.trans hi
  have outside (i : I) (hi : i∈Aᶜ) (j : Fin (n i+1)) : f ⟨i,j⟩∈Tᶜ :=
    fun h => hi ((component_of_star_vertex G n f i j).trans h)
  let a := restrictStarCopy G n f A T inside
  let b := restrictStarCopy G n f Aᶜ Tᶜ outside
  have ca := forest_copy_matching (G.induce T) _ (fun i:A => pn i.val) ⟨a⟩
  have cb := forest_copy_matching (G.induce Tᶜ) _ (fun i : ↥(Aᶜ) => pn i.val) ⟨b⟩
  rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at ca cb
  have sum := Set.ncard_add_ncard_compl A
  rw [Nat.card_eq_fintype_card] at sum
  have tot := JSP452Audit.StarHost.rank_component_sides G T (fun _ hx _ hy edge => hy ((c.mem_supp_congr_adj edge).mp hx))
  have rank : A.ncard=matchingEdges (G.induce T) := by omega
  have size := Nat.card_le_card_of_injective a a.injective
  change Nat.card (Σi:A, Fin (n i.val + 1)) ≤ Nat.card c.supp at size
  rw [Nat.card_sigma] at size
  simp only [Nat.card_fin] at size
  exact ⟨rank,by rwa [finsum_eq_sum_of_fintype]⟩

#print axioms star_load_at_matching_rank
end JSP452Audit.StarHost
