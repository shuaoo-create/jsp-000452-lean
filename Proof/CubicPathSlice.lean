import CubicGreedyTerminalBridge
import DegreeTwoComponents
import TightComponentSizes
namespace JSP452Audit.StarHost
open SimpleGraph
namespace CubicPairFamily
variable {X I : Type*} [Fintype X] [Fintype I]

def PaidRemoval (P:CubicPairFamily X I) (G:SimpleGraph X) (U:Set X) : Prop :=
  ∃T S:Set X,T⊆U ∧ T.Nonempty ∧ (∀x∈T,x∈S ∨ ∃w∈S,G.Adj x w) ∧
    5*S.ncard+P.residualCost G U≤5*T.ncard+P.residualCost G (U\T)

theorem removal_of_cross_price (P:CubicPairFamily X I) (G:SimpleGraph X) (U T S:Set X)
    (sub:T⊆U) (pos:T.Nonempty) (hits:∀x∈T,x∈S ∨ ∃w∈S,G.Adj x w)
    (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3)
    (price:5*S.ncard+3*T.ncard+crossCount G T (U\T)≤5*T.ncard+(P.active T).card) : P.PaidRemoval G U := by
  have cut := P.residual_cost_removal G U T sub (fun x hx => cap x (sub hx))
  exact ⟨T,S,sub,pos,hits,by omega⟩

end CubicPairFamily
variable {X : Type*} [Fintype X]

theorem internal_cross_account (G:SimpleGraph X) (U T:Set X) (sub:T⊆U) :
    fourLabelSum T (fourWhiteDegree G U)=2*(G.induce T).edgeSet.ncard+crossCount G T (U\T) := by
  let R := U\T
  have dis : Disjoint T R := Set.disjoint_sdiff_right
  have whole : T∪R=U := by rw [Set.union_comm];exact Set.sdiff_union_of_subset sub
  have split : fourWhiteDegree G U=(fun x => fourWhiteDegree G T x+fourWhiteDegree G R x) := by
    funext x;rw [←four_degree_split G T R dis,whole]
  rw [split,four_sum_add,four_sum_cross,four_sum_cross,crossCount_self]

/-- A concrete path in the original white labels has at least n-1 genuine
internal edges. The chosen indices which cover the path lift to its labels. -/
theorem path_slice_internal {n:ℕ} (G:SimpleGraph X) (v:Fin n ↪ X)
    (edges : ∀i j,(pathGraph n).Adj i j → G.Adj (v i) (v j)) :
    n-1≤(G.induce (Set.range v)).edgeSet.ncard := by
  let T := Set.range v
  let cp : (pathGraph n).Copy (G.induce T) := ⟨⟨fun i => ⟨v i,Set.mem_range_self i⟩,fun e => edges _ _ e⟩,
    fun _ _ eq => v.injective (congrArg (fun z:↥T => z.val) eq)⟩
  have bound := Nat.card_le_card_of_injective cp.mapEdgeSet cp.mapEdgeSet.injective
  rw [Nat.card_coe_set_eq,Nat.card_coe_set_eq,path_edge_ncard] at bound;exact bound

theorem path_slice_cover {n:ℕ} (G:SimpleGraph X) (v:Fin n ↪ X)
    (edges : ∀i j,(pathGraph n).Adj i j → G.Adj (v i) (v j)) (C:Finset (Fin n))
    (cover : ∀i:Fin n,i∈C ∨ ∃j∈C,(pathGraph n).Adj i j) :
    ∃S:Set X,S.ncard≤C.card ∧ ∀x∈Set.range v,x∈S ∨ ∃w∈S,G.Adj x w := by
  let S := v '' (C:Set (Fin n))
  have size := Set.ncard_image_le (f:=v) (s:=(C:Set (Fin n)))
  rw [Set.ncard_coe_finset] at size
  refine ⟨S,size,?_⟩
  rintro _ ⟨i,rfl⟩
  rcases cover i with mem|⟨j,jc,e⟩
  · exact Or.inl ⟨i,mem,rfl⟩
  · exact Or.inr ⟨v j,⟨j,jc,rfl⟩,edges i j e⟩

#print axioms internal_cross_account
#print axioms path_slice_internal
#print axioms path_slice_cover
end JSP452Audit.StarHost
