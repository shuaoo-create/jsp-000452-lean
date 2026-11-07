import ZeroCutDegree
import PartitionHandshake
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem one_cut_side {X : Type*} [Finite X] (K : SimpleGraph X) (u : X) (A : Finset X)
    (pop : A.Nonempty) (closed : ∀x∈A,∀y,K.Adj x y → y=u ∨ y∈A)
    (D : ℕ) (b : X→ℕ) (pos : ∀x,1≤b x)
    (degree : ∀x,Nat.card (K.neighborSet x)+b x=D) :
    D-1≤∑x∈A,b x := by
  classical
  have npos := Finset.card_pos.mpr pop
  by_cases long : D-1≤A.card
  · have charge := Finset.sum_le_sum (s:=A) (fun x _ => pos x)
    simpa using long.trans (show A.card≤∑x∈A,b x by simpa using charge)
  have low (x:X) (hx:x∈A) : D-A.card≤b x := by
    let U := insert u (A.erase x)
    have sub : K.neighborSet x⊆(U : Set X) := by
      intro y adj
      rcases closed x hx y adj with eq|inA
      · exact Finset.mem_insert.mpr (Or.inl eq)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨(show K.Adj x y from adj).ne.symm,inA⟩))
    have bound := Set.ncard_le_ncard sub
    rw [←Nat.card_coe_set_eq,Set.ncard_coe_finset] at bound
    have add := Finset.card_insert_le u (A.erase x)
    rw [Finset.card_erase_of_mem hx] at add
    have d := degree x
    change Nat.card (K.neighborSet x)≤(insert u (A.erase x)).card at bound
    omega
  have cost := Finset.sum_le_sum (s:=A) (fun x hx => low x hx)
  simp only [Finset.sum_const,nsmul_eq_mul] at cost
  change A.card*(D-A.card)≤∑x∈A,b x at cost
  have room : A.card≤D := by omega
  have eq := Nat.sub_add_cancel room
  obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (show A.card≠0 by omega)
  obtain ⟨b',hb⟩ := Nat.exists_eq_succ_of_ne_zero (show D-A.card≠0 by omega)
  rw [hb,ha,Nat.succ_mul,Nat.mul_succ] at cost
  omega

/-- Any cut vertex separates two nonempty sides. Counting one external
neighbor per vertex on a large side, or the internal degree cap on a
small side, charges D−1 to each side and one more to the cut vertex. -/
private theorem cut_spends_boundary {X : Type*} [Fintype X] (K : SimpleGraph X)
    (u : X) (cut : ¬(K.induce {v | v≠u}).Preconnected) (D : ℕ) (b : X→ℕ)
    (pos : ∀x,1≤b x) (degree : ∀x,Nat.card (K.neighborSet x)+b x=D) :
    2*D-1≤∑x,b x := by
  classical
  let H := K.induce {v | v≠u}
  change ¬∀x y,H.Reachable x y at cut
  push Not at cut
  obtain ⟨x,y,apart⟩ := cut
  let A := Finset.univ.filter (fun v => ∃h:v≠u,H.Reachable x ⟨v,h⟩)
  let B := Finset.univ.filter (fun v => v≠u ∧ v∉A)
  have xIn : x.val∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.property,Reachable.refl _⟩
  have yIn : y.val∈B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,y.property,fun h =>
    apart (Finset.mem_filter.mp h).2.choose_spec⟩
  have sep {a b:X} (ha:a∈A) (hb:b∈B) : ¬K.Adj a b := by
    obtain ⟨ah,reach⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨bh,notA⟩ := (Finset.mem_filter.mp hb).2
    intro edge
    exact notA (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bh,
      reach.trans (show H.Adj ⟨a,ah⟩ ⟨b,bh⟩ from edge).reachable⟩)
  have ca : ∀a∈A,∀v,K.Adj a v → v=u ∨ v∈A := by
    intro a ha v edge
    by_contra! contrary
    exact sep ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,contrary⟩) edge
  have cb : ∀a∈B,∀v,K.Adj a v → v=u ∨ v∈B := by
    intro a ha v edge
    by_cases eq : v=u
    · exact Or.inl eq
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq,fun inside => sep inside ha edge.symm⟩)
  have da := one_cut_side K u A ⟨_,xIn⟩ ca D b pos degree
  have db := one_cut_side K u B ⟨_,yIn⟩ cb D b pos degree
  have dis : Disjoint A B := Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_filter.mp hb).2.2 ha)
  have uAway : u∉A∪B := by
    intro h
    rcases Finset.mem_union.mp h with ha|hb
    · exact (Finset.mem_filter.mp ha).2.choose rfl
    · exact (Finset.mem_filter.mp hb).2.1 rfl
  have combined := Finset.sum_le_sum_of_subset_of_nonneg (f:=b)
    (Finset.subset_univ (insert u (A∪B))) (by intros; omega)
  rw [Finset.sum_insert uAway,Finset.sum_union dis] at combined
  have hu := pos u
  omega

/-- An original D-regular graph pays at least 2D−1 crossing edges for
a block whose every vertex has an external neighbor and whose deletion
of one internal vertex splits the block. -/
theorem cut_vertex_boundary_of_external_neighbor {V : Type*} [Finite V]
    (Q : SimpleGraph V) (B : Set V) (D : ℕ) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (u : B) (cut : ¬((Q.induce B).induce {v | v≠u}).Preconnected)
    (ext : ∀x:B,∃y∈Bᶜ,Q.Adj x.val y) : 2*D-1≤crossCount Q B Bᶜ := by
  classical
  let _ := Fintype.ofFinite B
  let b (x:B) := (Q.neighborSet x.val∩Bᶜ).ncard
  have positive (x:B) : 1≤b x := by
    obtain ⟨y,out,edge⟩ := ext x
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨y,edge,out⟩
  have degree (x:B) : Nat.card ((Q.induce B).neighborSet x)+b x=D := by
    let N := Q.neighborSet x.val
    have split : (N∩B)∪(N∩Bᶜ)=N := by rw [←Set.inter_union_distrib_left,Set.union_compl_self,Set.inter_univ]
    have apart : Disjoint (N∩B) (N∩Bᶜ) := disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
    have count := congrArg Set.ncard split
    rw [Set.ncard_union_eq apart] at count
    rw [induced_degree_intersection]
    exact count.trans ((Nat.card_coe_set_eq N).symm.trans (reg x.val))
  rw [crossCount_eq_neighbor_sum]
  exact cut_spends_boundary (Q.induce B) u cut D b positive degree

/-- A cardinal-maximum independent set guarantees the exterior
neighbors needed above for every block disjoint from it. -/
theorem cut_vertex_boundary_outside_largest_independent {V : Type*} [Finite V]
    (Q : SimpleGraph V) (I B : Set V) (D : ℕ) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (ind : Q.IsIndepSet I) (largest : ∀J:Set V,Q.IsIndepSet J → J.ncard≤I.ncard)
    (away : Disjoint I B) (u : B) (cut : ¬((Q.induce B).induce {v | v≠u}).Preconnected) :
    2*D-1≤crossCount Q B Bᶜ := by
  apply cut_vertex_boundary_of_external_neighbor Q B D reg u cut
  intro x
  by_contra! isolated
  have xi : x.val∉I := fun mem => Set.disjoint_left.mp away mem x.property
  have larger : Q.IsIndepSet (insert x.val I) := by
    rintro a (ha|ha) b (hb|hb) diff edge
    · exact diff (ha.trans hb.symm)
    · exact isolated b (fun h => Set.disjoint_left.mp away hb h) (ha ▸ edge)
    · exact isolated a (fun h => Set.disjoint_left.mp away ha h) (hb ▸ edge.symm)
    · exact ind ha hb diff edge
  have stop := largest _ larger
  rw [Set.ncard_insert_of_notMem xi] at stop
  omega

#print axioms cut_vertex_boundary_of_external_neighbor
#print axioms cut_vertex_boundary_outside_largest_independent
end JSP452Audit.StarHost

