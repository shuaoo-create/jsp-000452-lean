import FinalSubcapSingleBoundaryExcluded
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- If both original heads lie below the cap, neither side embeds in
any ordinary core of this same source. -/
theorem strict_subcap_heads_force_double_escape (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    F.n ⟨0,F.hs⟩<D → F.m ⟨0,F.ht⟩<D → μ<min F.s F.t := by
  intro D μ nc mc
  let d := F.rank-matchingEdges F.G
  have six : 6≤D := minimal_subcap_heads_force_degree_six F paid nc mc
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have res := (minimal_strict_source_deficit F paid).2.1
  have guard := strict_exterior_endpoint_guards F paid K
  have kinds := strict_single_unpaid_types F paid K
  have missing := strict_source_missing_heights F paid K
  have sources := strict_common_actual_successors F paid K
  have boundary := strict_subcap_single_forces_top_boundary F paid K nc mc
  have any := strict_source_one_list_escapes F paid K
  change μ+d<max F.s F.t at any
  by_contra! no
  by_cases e : μ<F.s
  · have inside : F.t≤μ := by omega
    exact final_subcap_single_impossible F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.live six cap top
      (boundary.1 e inside) d width res (guard.1 e) e inside (kinds.1 e inside) (missing.1 e) (sources.1 e)
  · have inside : F.s≤μ := by omega
    have esc : μ<F.t := by omega
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have eq := row_energy_colour_swap F.m F.n F.r
    exact final_subcap_single_impossible F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn (by rw [swap];exact F.live)
      six cap ((diagonal_swap _ _ _).trans top) (boundary.2 esc inside) d ((highest_width_colour_swap _ _ _).le.trans width)
      res (guard.2 esc) esc inside (kinds.2 esc inside) (missing.2 esc) (by rw [swap,eq];exact sources.2 esc)

def RemainingOriginalRegimes (F : StrictFamily.{u}) : Prop :=
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  (F.n ⟨0,F.hs⟩=D ∧ ∀K:DegreeRegion F.G D,
      F.t≤matchingEdges (F.G.induce K.core) ∧ matchingEdges (F.G.induce K.core)+K.roots.ncard+F.r+d+1≤F.s ∧
      F.t≤matchingEdges (F.G.induce K.rest) ∧ (∀j,F.m j<D)) ∨
  (F.m ⟨0,F.ht⟩=D ∧ ∀K:DegreeRegion F.G D,
      F.s≤matchingEdges (F.G.induce K.core) ∧ matchingEdges (F.G.induce K.core)+K.roots.ncard+F.r+d+1≤F.t ∧
      F.s≤matchingEdges (F.G.induce K.rest) ∧ (∀i,F.n i<D)) ∨
  (6≤D ∧ (∀i,F.n i<D) ∧ (∀j,F.m j<D) ∧ ∀K:DegreeRegion F.G D,
      matchingEdges (F.G.induce K.core)+K.roots.ncard+F.r+d+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges (F.G.induce K.rest))

theorem strict_original_regimes (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) : RemainingOriginalRegimes F := by
  let D := diagonal F.n F.m (F.r+2)-1
  by_cases red : F.n ⟨0,F.hs⟩=D
  · exact Or.inl ⟨red,fun K => (strict_full_head_unique_escape F paid K).1 red⟩
  by_cases blue : F.m ⟨0,F.ht⟩=D
  · exact Or.inr (Or.inl ⟨blue,fun K => (strict_full_head_unique_escape F paid K).2 blue⟩)
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have lowR : F.n ⟨0,F.hs⟩<D := by have := nc ⟨0,F.hs⟩;omega
  have lowB : F.m ⟨0,F.ht⟩<D := by have := mc ⟨0,F.ht⟩;omega
  refine Or.inr (Or.inr ⟨minimal_subcap_heads_force_degree_six F paid lowR lowB,
    fun i => (F.hn (show (⟨0,F.hs⟩:Fin F.s) ≤ i from Nat.zero_le _)).trans_lt lowR,
    fun j => (F.hm (show (⟨0,F.ht⟩:Fin F.t) ≤ j from Nat.zero_le _)).trans_lt lowB,?_⟩)
  intro K
  have pair := strict_double_escape_data F paid K (strict_subcap_heads_force_double_escape F paid K lowR lowB)
  exact ⟨pair.1,pair.2.1⟩

/-- Failure of the original Ramsey identity would require either a
unique escaping full head, or two subcap escaping lists in every
ordinary region. No double-subcap single-escape branch remains. -/
theorem original_failure_two_remaining_regimes {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 4≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ RemainingOriginalRegimes F := by
  obtain ⟨F,paid,deg,edges,order,_⟩ := original_failure_needs_degree_four.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,deg,edges,order,strict_original_regimes F paid⟩

#print axioms strict_subcap_heads_force_double_escape
#print axioms strict_original_regimes
#print axioms original_failure_two_remaining_regimes
end JSP452Audit.StarHost
