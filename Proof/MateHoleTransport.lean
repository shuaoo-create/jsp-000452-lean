import UnpaidMateDecomposition
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- A clique away from the original mate labels pulls back to the genuine
clique away from the holes of the restricted matching. -/
theorem pullback_mate_antineighborhood_clique (G : SimpleGraph X) (I : Set X)
    (N : (G.induce Iᶜ).Subgraph) (W : Set X)
    (labels : Subtype.val '' N.vertsᶜ=W) (clique : G.IsClique (mateAntineighborhood G W)) :
    (G.induce Iᶜ).IsClique (mateAntineighborhood (G.induce Iᶜ) N.vertsᶜ) := by
  have lift (x : ↥(Iᶜ : Set X)) (hx : x∈mateAntineighborhood (G.induce Iᶜ) N.vertsᶜ) :
      x.val∈mateAntineighborhood G W := by
    constructor
    · rintro inside
      rw [←labels] at inside
      obtain ⟨y,hy,eq⟩ := inside
      exact hx.1 ((Subtype.ext eq : y=x) ▸ hy)
    · intro w hw
      rw [←labels] at hw
      obtain ⟨y,hy,rfl⟩ := hw
      exact hx.2 y hy
  intro x hx y hy ne
  exact clique (lift x hx) (lift y hy) (fun eq => ne (Subtype.ext eq))

/-- The original W-neighbors are exactly the original labels of the actual
uncovered neighbors of the residual point. -/
theorem original_mate_neighbor_labels (G : SimpleGraph X) (I : Set X)
    (N : (G.induce Iᶜ).Subgraph) (W : Set X) (labels : Subtype.val '' N.vertsᶜ=W)
    (x : ↥(Iᶜ : Set X)) :
    Subtype.val '' ((G.induce Iᶜ).neighborSet x ∩ N.vertsᶜ)=G.neighborSet x.val ∩ W := by
  ext w
  constructor
  · rintro ⟨y,⟨adj,hole⟩,rfl⟩
    exact ⟨adj,labels ▸ ⟨y,hole,rfl⟩⟩
  · rintro ⟨adj,hw⟩
    rw [← labels] at hw
    obtain ⟨y,hole,rfl⟩ := hw
    exact ⟨y,⟨adj,hole⟩,rfl⟩

theorem original_mate_neighbor_count (G : SimpleGraph X) (I : Set X)
    (N : (G.induce Iᶜ).Subgraph) (W : Set X) (labels : Subtype.val '' N.vertsᶜ=W)
    (x : ↥(Iᶜ : Set X)) :
    ((G.induce Iᶜ).neighborSet x ∩ N.vertsᶜ).ncard=(G.neighborSet x.val ∩ W).ncard := by
  rw [←original_mate_neighbor_labels G I N W labels x,Set.ncard_image_of_injective _ Subtype.val_injective]

/-- Both the same maximum residual matching and the required residual clique
are available for every near-perfect matching in the actual zero-reserve host. -/
theorem residual_mate_clique [Finite X] (Q : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0)
    (I : Set X) (ind : Q.IsIndepSet I)
    (max : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (v : X) (vi : v∈I) (M : Q.Subgraph) (hm : M.IsMatching) (expose : M.verts={x|x≠v}) :
    let N := restrictedOutsideMatching Q I M
    N.IsMatching ∧ N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ) ∧
      (Q.induce Iᶜ).IsClique (mateAntineighborhood (Q.induce Iᶜ) N.vertsᶜ) := by
  intro N
  obtain ⟨hn,rank,labels,count,indW⟩ := independent_mate_barrier Q D pos reg crit zero I ind v vi M hm expose
  exact ⟨hn,rank,pullback_mate_antineighborhood_clique Q I N _ labels
    (mate_antineighborhood_clique Q I _ ind max indW count)⟩

#print axioms pullback_mate_antineighborhood_clique
#print axioms residual_mate_clique
end JSP452Audit.StarHost
