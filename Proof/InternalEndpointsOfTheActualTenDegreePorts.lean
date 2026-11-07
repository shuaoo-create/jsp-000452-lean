import ExactEdgeAndMatchingAccountsForTheCombinedPortSupport
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {R:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G R h)

def innerTips : Set X := {x | x∈W.support ∧ ∃y,y∉W.support ∧ G.Adj x y}
theorem tip_count : W.innerTips.ncard≤W.portCount := by
  classical
  let outside (v:W.innerTips) := v.property.2.choose
  have pick (v:W.innerTips) : outside v∉W.support ∧ G.Adj v.val (outside v) := v.property.2.choose_spec
  let lift (v:W.innerTips) : {p:↥W.support × ↥(W.supportᶜ:Set X) // G.Adj p.1.val p.2.val} :=
    ⟨(⟨v.val,v.property.1⟩,⟨outside v,(pick v).1⟩),(pick v).2⟩
  exact Nat.card_le_card_of_injective lift (fun _ _ eq => Subtype.ext (congrArg (fun z => z.val.1.val) eq))

theorem ordinary_neighbors_stay {v x:X} (inside:v∈W.support) (unmarked:v∉W.innerTips) (edge:G.Adj v x) : x∈W.support := by
  by_contra out;exact unmarked ⟨inside,x,out,edge⟩

theorem ordinary_center_or_marked_leaf {v x:X} (edge:W.piece.Adj v x) : v∈W.support ∨ x∈W.innerTips := by
  by_cases inside:v∈W.support
  · exact Or.inl inside
  · have land : x∈W.support := by by_contra miss;exact edge.2 ⟨inside,miss⟩
    exact Or.inr ⟨land,v,inside,edge.1.symm⟩

#print axioms tip_count
#print axioms ordinary_neighbors_stay
#print axioms ordinary_center_or_marked_leaf
end JSP452Audit.StarHost.TenPortSupport
