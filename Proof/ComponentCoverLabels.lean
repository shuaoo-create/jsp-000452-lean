import ExteriorCoverFloor
import RegularIndependentReserve
import PositiveSelection
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Labels of a chosen original component belonging to a specified set. -/
def pieceLabels (G : SimpleGraph X) (S C : Set X)
    (c : (G.induce Sᶜ).ConnectedComponent) : Set c.supp :=
  {v | v.val.val∈C}

/-- An exact sum of restricted labels on the original selected components. -/
theorem selected_label_count (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) [Fintype T] (C : Set X) :
    (regionCore G S T ∩ C).ncard = ∑ c : T, (pieceLabels G S C c.val).ncard := by
  let f : (Σ c:T, ↥(pieceLabels G S C c.val)) → ↥(regionCore G S T ∩ C) :=
    fun ⟨c,v⟩ => ⟨v.val.val.val,⟨v.val.val,rfl,((c.val.mem_supp_iff _).mp v.val.property).symm ▸ c.property⟩,v.property⟩
  have inj : Function.Injective f := by
    rintro ⟨⟨c,hc⟩,⟨⟨x,hx⟩,xc⟩⟩ ⟨⟨b,hb⟩,⟨⟨y,hy⟩,yc⟩⟩ eq
    have vals : x=y := Subtype.ext (congrArg (fun z : ↥(regionCore G S T ∩ C) => z.val) eq)
    subst y
    have same : c=b := ((c.mem_supp_iff _).mp hx).symm.trans ((b.mem_supp_iff _).mp hy)
    subst b;rfl
  have surj : Function.Surjective f := by
    rintro ⟨_,⟨x,rfl,piece⟩,xc⟩
    exact ⟨⟨⟨_,piece⟩,⟨⟨x,rfl⟩,xc⟩⟩,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨inj,surj⟩)).symm.trans Nat.card_sigma

/-- Uncovered labels that have no internal core neighbor. -/
def freeCoreLabels (G : SimpleGraph X) (U C : Set X) : Set X :=
  {x | x∈U ∧ x∉C ∧ ∀ y∈U, ¬ G.Adj x y}

theorem component_cover_account (G : SimpleGraph X) {D : ℕ} (K : DegreeRegion G D)
    (C : Set X) (cover : G.IsVertexCover C) (c : K.pieces) :
    Nat.card c.val.supp+1 ≤ 2*(pieceLabels G K.barrier C c.val).ncard+
      2*(pieceLabels G K.barrier (freeCoreLabels G K.core C) c.val).ncard := by
  let Q := (G.induce K.barrierᶜ).induce c.val.supp
  let I := pieceLabels G K.barrier C c.val
  let J := pieceLabels G K.barrier (freeCoreLabels G K.core C) c.val
  let v : c.val.supp := ⟨_,c.val.nonempty_supp.choose_spec⟩
  have ord := factorCritical_order_rank Q (K.critical c.val).2 v
  change Nat.card c.val.supp+1≤2*I.ncard+2*J.ncard
  by_cases present : I.Nonempty
  · have cv : Q.IsVertexCover I := fun _ _ e => cover e
    have floor := factorCritical_cut_rank Q (K.critical c.val).2 I present
    rw [cover_residual_empty Q I cv,matchingEdges_bot] at floor
    omega
  · have every (x : c.val.supp) : x∈J := by
      have xcore : x.val.val ∈ K.core :=
        ⟨x.val,rfl,((c.val.mem_supp_iff _).mp x.property).symm ▸ c.property⟩
      have outside (z : c.val.supp) : z.val.val∉C := fun h => present ⟨z,h⟩
      refine ⟨xcore,outside x,?_⟩
      rintro _ ⟨y,rfl,_⟩ adj
      have e : (G.induce K.barrierᶜ).Adj x.val y := adj
      have mem := (c.val.mem_supp_congr_adj e).mp x.property
      exact (cover adj).elim (outside x) (outside ⟨y,mem⟩)
    have all : J=Set.univ := Set.eq_univ_of_forall every
    rw [all,Set.ncard_univ]
    have pos : 0<Nat.card c.val.supp := by
      let _ : Nonempty c.val.supp := ⟨v⟩
      exact Nat.card_pos
    omega

#print axioms selected_label_count
#print axioms component_cover_account
end JSP452Audit.StarHost
