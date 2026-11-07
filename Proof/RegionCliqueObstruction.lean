import CliqueBoundary
import DegreeRegion

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Hall bound for any chosen family of small full cliques, using only its own adjacent roots. -/
theorem region_cliques_hall {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (K : DegreeRegion G D)
    (B : Set (G.induce K.barrierᶜ).ConnectedComponent) (subset : B ⊆ K.pieces)
    (all : ∀ c ∈ B, ((G.induce K.barrierᶜ).induce c.supp)=⊤ ∧ Nat.card c.supp ≤ D) :
    B.ncard ≤ (rootNeighbors (rootIncidence G K.barrier) B).ncard := by
  classical
  let I := ↥B
  let _ := Fintype.ofFinite I
  let C (i : I) : Set X := Subtype.val '' i.val.supp
  have card (i : I) : (C i).ncard = Nat.card i.val.supp :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have apart (i j : I) (ne : i≠j) : Disjoint (C i) (C j) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨b,hb,e⟩
    have eq : b=a := Subtype.ext e
    have ha' : (G.induce K.barrierᶜ).connectedComponentMk a=i.val := ha
    have hb' : (G.induce K.barrierᶜ).connectedComponentMk b=j.val := hb
    exact ne (Subtype.ext (ha'.symm.trans (eq ▸ hb')))
  have clique (i : I) : G.IsClique (C i) := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ ne
    let v : i.val.supp := ⟨a,ha⟩
    let w : i.val.supp := ⟨b,hb⟩
    change ((G.induce K.barrierᶜ).induce i.val.supp).Adj v w
    rw [(all i.val i.property).1]
    exact fun eq => ne (congrArg (fun p : i.val.supp => p.val.val) eq)
  have full (i : I) (x : X) (hx : x∈C i) : Nat.card (G.neighborSet x) = D := by
    rcases hx with ⟨a,ha,rfl⟩
    exact K.full (subset i.property) ⟨a,ha⟩
  have positive (i : I) : 1 ≤ (C i).ncard := by
    let _ : Nonempty i.val.supp := i.val.nonempty_supp.to_subtype
    rw [card]; exact Nat.card_pos
  have external (i : I) (x : X) (hx : x∈C i) (y : X) (edge : G.Adj x y) (out : y∉C i) :
      y∈regionRoots G K.barrier B := by
    rcases hx with ⟨a,ha,rfl⟩
    by_cases hy : y∈K.barrier
    · exact ⟨⟨y,hy⟩,⟨i.val,i.property,⟨a,ha⟩,edge.symm⟩,rfl⟩
    · let b : ↥K.barrierᶜ := ⟨y,hy⟩
      have adj : (G.induce K.barrierᶜ).Adj a b := edge
      exact (out ⟨b,(i.val.mem_supp_congr_adj adj).mp ha,rfl⟩).elim
  have bounded := clique_family_le_roots G C (regionRoots G K.barrier B) D pos apart clique full positive
    (fun i => (card i).le.trans (all i.val i.property).2) external (fun x _ => cap x)
  change B.ncard ≤ (regionRoots G K.barrier B).ncard at bounded
  have nroot : (regionRoots G K.barrier B).ncard = (rootNeighbors (rootIncidence G K.barrier) B).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  exact bounded.trans_eq nroot

/-- Specializing to the whole balanced family forces zero exposure. -/
theorem region_cliques_zero_exposure {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (K : DegreeRegion G D)
    (all : ∀ c ∈ K.pieces, ((G.induce K.barrierᶜ).induce c.supp)=⊤ ∧ Nat.card c.supp ≤ D) :
    minimumExposure G D = 0 := by
  have bounded := region_cliques_hall G D pos cap K K.pieces Set.Subset.rfl all
  have balanced := K.balanced
  omega

#print axioms region_cliques_hall
#print axioms region_cliques_zero_exposure
end JSP452Audit.StarHost
