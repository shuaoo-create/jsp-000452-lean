import CubicMatchingCover
import ZeroCutDegree
namespace JSP452Audit.StarHost
open SimpleGraph
namespace CubicPairFamily
variable {X I : Type*} [Fintype X] [Fintype I]

/-- If surviving ordinary white edges already form a matching, the
labelled edge count and the same maximum matching pay the full terminal. -/
theorem matching_residual_paid (P:CubicPairFamily X I) (G:SimpleGraph X) (U:Set X)
    (cap : ∀v∈U,fourWhiteDegree G U v+P.degree U v≤3)
    (one : ∀v∈U,fourWhiteDegree G U v≤1)
    (centers : ∀j∈P.active U,∃w:X,G.Adj (P.left j) w ∧ G.Adj (P.right j) w) :
    ∃S:Set X,(∀v∈U,v∈S ∨ ∃w∈S,G.Adj v w) ∧
      5*S.ncard+P.residualCost G U≤5*U.ncard := by
  classical
  let Q := G.induce U
  let _ := Fintype.ofFinite Q.edgeSet
  let white := ofGraph Q
  let paired := P.inside U
  let family := white.combine paired
  let K := family.supportGraph
  have land (i:Q.edgeSet⊕↥(P.active U)) : K.Adj (family.left i) (family.right i) :=
    ⟨i,Or.inl ⟨rfl,rfl⟩⟩
  have whiteAdj (e:Q.edgeSet) : Q.Adj (white.left e) (white.right e) := by
    change s(graphEnds Q e false,graphEnds Q e true)∈Q.edgeSet
    rw [graphEnds_edge Q e];exact e.property
  have sub : Q≤K := by
    intro x y adj
    let e : Q.edgeSet := ⟨s(x,y),adj⟩
    have eq := graphEnds_edge Q e
    change s(white.left e,white.right e)=s(x,y) at eq
    rcases Sym2.eq_iff.mp eq with lr|rl
    · exact ⟨Sum.inl e,Or.inl ⟨lr.1.symm,lr.2.symm⟩⟩
    · exact ⟨Sum.inl e,Or.inr ⟨rl.2.symm,rl.1.symm⟩⟩
  have degree (x:U) : family.degree Set.univ x≤3 := by
    rw [combine_degree,graph_pair_degree,inside_degree]
    change Nat.card ((G.induce U).neighborSet x)+_≤3
    rw [induced_degree_intersection]
    exact cap x.val x.property
  have rank := family.labelled_edges_le_four_rank K land degree
  rw [Fintype.card_sum,Fintype.card_coe,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at rank
  change Q.edgeSet.ncard+(P.active U).card≤4*matchingEdges K at rank
  let M : K.Subgraph := {
    verts := Q.support
    Adj := Q.Adj
    adj_sub := fun e => sub e
    edge_vert := fun e => ⟨_,e⟩
    symm := Q.symm
  }
  have matched : M.IsMatching := by
    intro x hx
    change x∈Q.support at hx
    obtain ⟨y,edge⟩ := hx
    refine ⟨y,edge,?_⟩
    intro z ez
    have small : (Q.neighborSet x).ncard≤1 := by
      rw [←Nat.card_coe_set_eq,induced_degree_intersection];exact one x.val x.property
    exact (Set.ncard_le_one (Set.toFinite _)).mp small z ez y edge
  have wrank := le_matchingEdges matched
  have same : M.edgeSet=Q.edgeSet := by ext e;induction e using Sym2.inductionOn with | _ u v => rfl
  rw [same] at wrank
  have both : P.residualCost G U≤5*matchingEdges K := by
    unfold residualCost
    rw [four_sum_cross,crossCount_self]
    change 2*Q.edgeSet.ncard+(P.active U).card≤5*matchingEdges K
    omega
  have realize (x y:U) (edge:K.Adj x y) :
      ∃w:X,(x.val=w ∨ G.Adj x.val w) ∧ (y.val=w ∨ G.Adj y.val w) := by
    obtain ⟨j,same|rev⟩ := edge
    · rcases same with ⟨rfl,rfl⟩
      cases j with
      | inl e => exact ⟨(white.left e).val,Or.inl rfl,Or.inr (whiteAdj e).symm⟩
      | inr q =>
        obtain ⟨w,l,r⟩ := centers q.val q.property
        exact ⟨w,Or.inr l,Or.inr r⟩
    · rcases rev with ⟨rfl,rfl⟩
      cases j with
      | inl e => exact ⟨(white.left e).val,Or.inr (whiteAdj e).symm,Or.inl rfl⟩
      | inr q =>
        obtain ⟨w,l,r⟩ := centers q.val q.property
        exact ⟨w,Or.inr r,Or.inr l⟩
  obtain ⟨S,hit,small⟩ := pair_matching_gives_cover G U K realize
  exact ⟨S,hit,by omega⟩

end CubicPairFamily
#print axioms CubicPairFamily.matching_residual_paid
end JSP452Audit.StarHost
