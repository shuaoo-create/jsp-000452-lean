import MateHoleTransport
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A largest independent set dominates each vertex outside it. -/
theorem largest_independent_dominates (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (max : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard) (a : X) (ha : a∉I) :
    ∃ z∈I,Q.Adj a z := by
  classical
  by_contra! none
  have bigger : Q.IsIndepSet (insert a I) := by
    rintro x (rfl|hx) y (rfl|hy) ne edge
    · exact ne rfl
    · exact none _ hy edge
    · exact none _ hx edge.symm
    · exact ind hx hy ne edge
  have bound := max _ bigger
  rw [Set.ncard_insert_of_notMem ha] at bound
  omega

/-- A clique outside a largest independent set needs at least one extra
neighbor at each vertex, so its size is bounded by the degree cap itself. -/
theorem outside_largest_clique_size (Q : SimpleGraph X) (I J : Set X) (ind : Q.IsIndepSet I)
    (max : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard) (outside : J⊆Iᶜ)
    (clique : Q.IsClique J) (D : ℕ) (cap : ∀x,Nat.card (Q.neighborSet x)≤D) :
    J.ncard≤D := by
  classical
  by_cases ne : J.Nonempty
  · obtain ⟨a,ha⟩ := ne
    obtain ⟨z,hz,az⟩ := largest_independent_dominates Q I ind max a (outside ha)
    have znot : z∉J := fun h => outside h hz
    have sub : insert z (J \ {a}) ⊆ Q.neighborSet a := by
      rintro x (rfl|hx)
      · exact az
      · exact clique ha hx.1 (fun eq => hx.2 (eq ▸ (Set.mem_singleton a)))
    have size := Set.ncard_le_ncard sub
    have zn : z∉J \ {a} := fun h => znot h.1
    rw [Set.ncard_insert_of_notMem zn, Set.ncard_sdiff_singleton_of_mem ha] at size
    have pos : 0 < J.ncard := (Set.ncard_pos (Set.toFinite J)).mpr ⟨a,ha⟩
    have c := cap a
    rw [Nat.card_coe_set_eq] at c
    omega
  · rw [Set.not_nonempty_iff_eq_empty.mp ne,Set.ncard_empty]
    exact Nat.zero_le _

/-- The untouched matching edges are the paper's M₂,₀. Their endpoints have
no neighbors among the uncovered labels, including at the opposite endpoint. -/
def zeroMateRegion {Y : Type*} (H : SimpleGraph Y) (N : H.Subgraph) : Set Y :=
  {x | ∃ y, N.Adj x y ∧ (∀w∈N.vertsᶜ, ¬H.Adj x w) ∧ (∀w∈N.vertsᶜ, ¬H.Adj y w)}

theorem zeroMateRegion_subset_anti {Y : Type*} (H : SimpleGraph Y) (N : H.Subgraph) :
    zeroMateRegion H N ⊆ mateAntineighborhood H N.vertsᶜ := by
  rintro x ⟨y,xy,noX,noY⟩
  exact ⟨fun hx => hx (N.edge_vert xy),noX⟩

/-- With original labels restored, the actual M₂,₀ region is a clique and
has at most D vertices, including the possibility that it is empty. -/
theorem original_zero_mate_region_bound (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (max : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (N : (Q.induce Iᶜ).Subgraph) (W : Set X) (labels : Subtype.val '' N.vertsᶜ=W)
    (indW : Q.IsIndepSet W) (gap : W.ncard+1=I.ncard)
    (D : ℕ) (cap : ∀x,Nat.card (Q.neighborSet x)≤D) :
    let T := Subtype.val '' zeroMateRegion (Q.induce Iᶜ) N
    Q.IsClique T ∧ T.ncard≤D := by
  intro T
  have cl := (pullback_mate_antineighborhood_clique Q I N W labels
    (mate_antineighborhood_clique Q I W ind max indW gap)).subset (zeroMateRegion_subset_anti _ _)
  have mapped : Q.IsClique T := by
    rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩ ne
    exact cl hx hy (fun eq => ne (congrArg Subtype.val eq))
  refine ⟨mapped,outside_largest_clique_size Q I T ind max ?_ mapped D cap⟩
  rintro x ⟨x,hx,rfl⟩
  exact x.property

#print axioms original_zero_mate_region_bound
end JSP452Audit.StarHost
