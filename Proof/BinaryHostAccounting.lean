import BinaryFlexDef

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u

/-- A graph invariant that adds over disjoint sums and vanishes on the empty vertex
type is the sum of its values on the actual connected components. -/
private theorem sum_of_components
    (f : {Y : Type u} → [Finite Y] → SimpleGraph Y → ℕ)
    (zero : ∀ {Y : Type u} [Finite Y] [IsEmpty Y] (G : SimpleGraph Y), f G = 0)
    (iso : ∀ {Y Z : Type u} [Finite Y] [Finite Z] {G : SimpleGraph Y} {H : SimpleGraph Z},
      G ≃g H → f G = f H)
    (add : ∀ {Y Z : Type u} [Finite Y] [Finite Z] (G : SimpleGraph Y) (H : SimpleGraph Z),
      f (G ⊕g H) = f G + f H) {X : Type u} [Finite X] (G : SimpleGraph X)
    [Fintype G.ConnectedComponent] : f G = ∑ c : G.ConnectedComponent, f c.toSimpleGraph := by
  classical
  let U (T : Finset G.ConnectedComponent) : Set X := {x | G.connectedComponentMk x ∈ T}
  have induct (T : Finset G.ConnectedComponent) : f (G.induce (U T)) = ∑ c ∈ T, f c.toSimpleGraph := by
    induction T using Finset.induction_on with
    | empty =>
      let _ : IsEmpty ↥(U ∅) := ⟨fun x => Finset.notMem_empty _ x.property⟩
      rw [zero,Finset.sum_empty]
    | @insert c T fresh ih =>
      have cover : c.supp ∪ U T = U (insert c T) := by ext x; exact Finset.mem_insert.symm
      have apart : Disjoint c.supp (U T) := Set.disjoint_left.mpr fun _ hx ht =>
        fresh ((show G.connectedComponentMk _ = c from hx) ▸ ht)
      have sep : ∀ x∈c.supp, ∀ y∈U T, ¬G.Adj x y := fun _ hx _ hy edge =>
        Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp hx) hy
      have split := iso (regionSumIso G (U (insert c T)) c.supp (U T) cover apart sep)
      rw [add,ih] at split
      rw [Finset.sum_insert fresh]; exact split.symm
  have result := induct Finset.univ
  have all : U Finset.univ = Set.univ := by ext; simp [U]
  rw [all] at result
  exact (iso (induceUnivIso G)).symm.trans result

private theorem empty_graph_eq_bot {X : Type*} [IsEmpty X] (G : SimpleGraph X) : G=⊥ := by
  ext x; exact isEmptyElim x

theorem host_component_totals {X : Type*} [Finite X] (G : SimpleGraph X) [Fintype G.ConnectedComponent] :
    (G.edgeSet.ncard = ∑ c : G.ConnectedComponent, c.toSimpleGraph.edgeSet.ncard) ∧
    (matchingEdges G = ∑ c : G.ConnectedComponent, matchingEdges c.toSimpleGraph) ∧
    (deletionBudget G 2 = ∑ c : G.ConnectedComponent, deletionBudget c.toSimpleGraph 2) := by
  refine ⟨?_,?_,?_⟩
  · exact sum_of_components (fun G => G.edgeSet.ncard) (fun G => by simp [empty_graph_eq_bot G])
      (fun e => Nat.card_congr e.mapEdgeSet) edge_ncard_sumGraph G
  · exact sum_of_components matchingEdges (fun G => by rw [empty_graph_eq_bot G,matchingEdges_bot])
      rank_eq_of_graph_iso matchingEdges_sumGraph G
  · exact sum_of_components (fun G => deletionBudget G 2)
      (fun G => by rw [empty_graph_eq_bot G,deletionBudget_bot 2 (by decide)])
      (fun e => deletionBudget_iso e 2) (fun G H => deletionBudget_sumGraph G H 2) G

/-- At every point of a genuine cycle of order at least three the degree is two.
Thus every missed vertex is a full-degree exposure, and an odd cycle must
pay at least one deletion at layer two. -/
theorem cycle_budget_two_exact (n : ℕ) (large : 3 ≤ n) : deletionBudget (cycleGraph n) 2 = n%2 := by
  let G := cycleGraph n
  have deg (x : Fin n) : Nat.card (G.neighborSet x)=2 := by
    revert x
    change ∀ x : Fin n, Nat.card ((cycleGraph n).neighborSet x)=2
    obtain ⟨m,he⟩ := Nat.exists_eq_add_of_le large
    rw [he,Nat.add_comm 3 m]; intro x
    rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,cycleGraph_degree_three_le]
  have upper := cycle_budget_two_bound n large
  by_contra! no
  have zero : deletionBudget G 2=0 := by change deletionBudget (cycleGraph n) 2=0; omega
  have exposed : minimumExposure G 2=0 :=
    (deletionBudget_zero_iff_minimumExposure_zero G 2 (by decide) (fun x => (deg x).le)).mp zero
  obtain ⟨M,hm,max,att⟩ := minimumExposure_attained G 2
  have all : exposedFull G M 2 = M.vertsᶜ := by
    ext x; change (x ∉ M.verts ∧ Nat.card (G.neighborSet x)=2) ↔ x ∉ M.verts; exact ⟨And.left,fun no => ⟨no,deg x⟩⟩
  rw [all,exposed] at att
  have ct := maximum_uncovered_count M hm max
  change M.vertsᶜ.ncard = minUnmatched G at ct
  rw [att,minUnmatched_eq_deficit,Nat.card_fin] at ct
  change 0 = n - 2 * matchingEdges (cycleGraph n) at ct
  rw [cycleGraph_matchingEdges] at ct
  omega

/-- On paths the rank pays for every edge. On an odd cycle the unmatched
one-edge deficit is paid by the second deletion layer. -/
theorem degree_two_edges_le_rank_budget {X : Type*} [Finite X] (G : SimpleGraph X)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) :
    G.edgeSet.ncard ≤ 2*matchingEdges G + deletionBudget G 2 := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have localBound (c : G.ConnectedComponent) : c.toSimpleGraph.edgeSet.ncard ≤
      2*matchingEdges c.toSimpleGraph + deletionBudget c.toSimpleGraph 2 := by
    rcases degree_two_component_classification G cap c with pathCase | cycleCase
    · obtain ⟨iso⟩ := pathCase
      have edges := Nat.card_congr iso.mapEdgeSet
      change (pathGraph _).edgeSet.ncard = c.toSimpleGraph.edgeSet.ncard at edges
      rw [path_edge_ncard] at edges
      rw [← rank_eq_of_graph_iso iso,pathGraph_matchingEdges]
      omega
    · obtain ⟨large,⟨iso⟩⟩ := cycleCase
      have edges := Nat.card_congr iso.mapEdgeSet
      change (cycleGraph _).edgeSet.ncard = c.toSimpleGraph.edgeSet.ncard at edges
      rw [cycle_edge_ncard _ large] at edges
      rw [← rank_eq_of_graph_iso iso,cycleGraph_matchingEdges,← deletionBudget_iso iso,
        cycle_budget_two_exact _ large]
      omega
  obtain ⟨edges,ranks,budgets⟩ := host_component_totals G
  rw [edges,ranks,budgets,Finset.mul_sum,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun c _ => localBound c)

private theorem component_order_two {X : Type*} [Finite X] (G : SimpleGraph X)
    (noIso : ∀ x, 0 < Nat.card (G.neighborSet x)) (c : G.ConnectedComponent) :
    2 ≤ Nat.card c.supp := by
  obtain ⟨x,mem⟩ := c.nonempty_supp
  have positive : 0 < (G.neighborSet x).ncard := noIso x
  obtain ⟨y,edge⟩ := (Set.ncard_pos (G.neighborSet x).toFinite).mp positive
  have adj : G.Adj x y := edge
  by_contra! small
  have bound : c.supp.ncard ≤ 1 := by change Nat.card c.supp ≤ 1; omega
  have same := (Set.ncard_le_one (s := c.supp)).mp bound x mem y ((c.mem_supp_congr_adj adj).mp mem)
  exact adj.ne same

/-- Every nonisolated path component has one more vertex than edge,
and has a positive matching rank. Cycle components have equal orders and sizes. -/
theorem degree_two_order_le_edges_pathCapacity {X : Type*} [Finite X] (G : SimpleGraph X)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) (noIso : ∀ x, 0 < Nat.card (G.neighborSet x)) :
    Nat.card X ≤ G.edgeSet.ncard + pathCapacity G := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have bounds (c : G.ConnectedComponent) :
      Nat.card c.supp ≤ c.toSimpleGraph.edgeSet.ncard +
        (if pathLike G c then matchingEdges c.toSimpleGraph else 0) := by
    rcases degree_two_component_classification G cap c with pathCase | cycleCase
    · obtain ⟨iso⟩ := pathCase
      have eq := Nat.card_congr iso.mapEdgeSet
      change (pathGraph _).edgeSet.ncard = c.toSimpleGraph.edgeSet.ncard at eq
      rw [path_edge_ncard] at eq
      have two := component_order_two G noIso c
      have path : pathLike G c := by unfold pathLike; omega
      rw [if_pos path,←rank_eq_of_graph_iso iso,pathGraph_matchingEdges]
      omega
    · obtain ⟨large,⟨iso⟩⟩ := cycleCase
      have eq := Nat.card_congr iso.mapEdgeSet
      change (cycleGraph _).edgeSet.ncard = c.toSimpleGraph.edgeSet.ncard at eq
      rw [cycle_edge_ncard _ large] at eq
      omega
  have order : Nat.card X = ∑ c : G.ConnectedComponent, Nat.card c.supp := by
    rw [← Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)).symm
  have total := (host_component_totals G).1
  dsimp only [pathCapacity]
  rw [order,total,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun c _ => bounds c)

private theorem transport_exact {X Y : Type*} [Finite X] [Finite Y] {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : G ≃g H) (source : ExactRankSplit G) : ExactRankSplit H := by
  intro u fits
  have rank := rank_eq_of_graph_iso e
  obtain ⟨R,sub,red,blue⟩ := source u (fits.trans_eq rank.symm)
  let P := R.comap e.symm
  refine ⟨P,fun _ _ adj => e.symm.map_rel_iff.mp (sub adj),?_,?_⟩
  · exact (rank_eq_of_graph_iso (SimpleGraph.Iso.comap e.symm.toEquiv R)).le.trans red
  · have eq : H \ P = (G \ R).comap e.symm := by
      ext x y
      change (H.Adj x y ∧ ¬R.Adj (e.symm x) (e.symm y)) ↔
        (G.Adj (e.symm x) (e.symm y) ∧ ¬R.Adj (e.symm x) (e.symm y))
      rw [e.symm.map_rel_iff]
    rw [eq,← rank]
    exact (rank_eq_of_graph_iso (SimpleGraph.Iso.comap e.symm.toEquiv (G \ R))).le.trans blue

theorem exactRankSplit_of_pathLike {X : Type*} [Finite X] (G : SimpleGraph X)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) (c : G.ConnectedComponent) (path : pathLike G c) :
    ExactRankSplit c.toSimpleGraph := by
  rcases degree_two_component_classification G cap c with pathCase | cycleCase
  · obtain ⟨iso⟩ := pathCase
    exact transport_exact iso (exactRankSplit_pathGraph _)
  · obtain ⟨large,⟨iso⟩⟩ := cycleCase
    have eq := Nat.card_congr iso.mapEdgeSet
    change (cycleGraph _).edgeSet.ncard = c.toSimpleGraph.edgeSet.ncard at eq
    rw [cycle_edge_ncard _ large] at eq
    unfold pathLike at path
    omega

#print axioms host_component_totals
#print axioms cycle_budget_two_exact
#print axioms degree_two_edges_le_rank_budget
#print axioms degree_two_order_le_edges_pathCapacity
#print axioms exactRankSplit_of_pathLike
end JSP452Audit.StarHost
