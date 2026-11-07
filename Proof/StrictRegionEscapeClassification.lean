import ExteriorTailLengthsAndPrice
namespace JSP452Audit.StarHost
universe u

/-- If both lists escape the same ordinary core, both heads are below the
degree, the degree is at least six, and the original exterior has enough
matching edges for the longer original list. -/
theorem strict_double_escape_data (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    let a := K.roots.ncard
    let d := F.rank-matchingEdges F.G
    μ<min F.s F.t → μ+a+F.r+d+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges (F.G.induce K.rest) ∧
      (∀i,F.n i<D) ∧ (∀j,F.m j<D) ∧ 6≤D := by
  intro D μ a d escape
  have actual := (strict_source_region_length_alternative F K).resolve_left (by omega)
  change μ+a+F.r+d+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges (F.G.induce K.rest) at actual
  obtain ⟨nl,ml⟩ := le_min_iff.mp actual.1
  have heads := strict_full_head_needs_root_core_capacity F paid K
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have nsub : F.n ⟨0,F.hs⟩<D := by
    have up := nc ⟨0,F.hs⟩
    by_contra! notSmall
    have eq : F.n ⟨0,F.hs⟩=D := by omega
    have bound := heads.1 eq
    change F.t≤μ+a+F.r at bound;omega
  have msub : F.m ⟨0,F.ht⟩<D := by
    have up := mc ⟨0,F.ht⟩
    by_contra! notSmall
    have eq : F.m ⟨0,F.ht⟩=D := by omega
    have bound := heads.2 eq
    change F.s≤μ+a+F.r at bound;omega
  exact ⟨actual.1,actual.2,fun i => (F.hn (show (⟨0,F.hs⟩:Fin F.s)≤ i from Nat.zero_le _)).trans_lt nsub,
    fun j => (F.hm (show (⟨0,F.ht⟩:Fin F.t)≤ j from Nat.zero_le _)).trans_lt msub,
    minimal_subcap_heads_force_degree_six F paid nsub msub⟩

/-- A full original head must occur on the unique escaping side, for every
ordinary region of the same source. The entire opposite list is embedded. -/
theorem strict_full_head_unique_escape (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    let a := K.roots.ncard
    let d := F.rank-matchingEdges F.G
    let k := matchingEdges (F.G.induce K.rest)
    (F.n ⟨0,F.hs⟩=D → F.t≤μ ∧ μ+a+F.r+d+1≤F.s ∧ F.t≤k ∧ (∀j,F.m j<D)) ∧
    (F.m ⟨0,F.ht⟩=D → F.s≤μ ∧ μ+a+F.r+d+1≤F.t ∧ F.s≤k ∧ (∀i,F.n i<D)) := by
  intro D μ a d k
  have escape := strict_source_one_list_escapes F paid K
  change μ+d<max F.s F.t at escape
  have single := single_embedded_side_heads_below_degree F paid K
  have lengths := strict_exterior_whole_tail_prices F paid K
  constructor
  · intro red
    have inner : F.t≤μ := by
      by_contra! out
      by_cases small : F.s≤μ
      · have never := single.1 small out ⟨0,F.hs⟩;omega
      · have pair := strict_double_escape_data F paid K (by change μ<min F.s F.t;omega)
        have bad := pair.2.2.1 ⟨0,F.hs⟩;omega
    have out : μ<F.s := by omega
    obtain ⟨_,_,_,len,_,rank⟩ := lengths.1 out
    exact ⟨inner,len,(le_max_right _ _).trans rank,single.2 inner out⟩
  · intro blue
    have inner : F.s≤μ := by
      by_contra! out
      by_cases small : F.t≤μ
      · have never := single.2 small out ⟨0,F.ht⟩;omega
      · have pair := strict_double_escape_data F paid K (by change μ<min F.s F.t;omega)
        have bad := pair.2.2.2.1 ⟨0,F.ht⟩;omega
    have out : μ<F.t := by omega
    obtain ⟨_,_,_,len,_,rank⟩ := lengths.2 out
    exact ⟨inner,len,(le_max_left _ _).trans rank,single.1 inner out⟩

#print axioms strict_double_escape_data
#print axioms strict_full_head_unique_escape
end JSP452Audit.StarHost
