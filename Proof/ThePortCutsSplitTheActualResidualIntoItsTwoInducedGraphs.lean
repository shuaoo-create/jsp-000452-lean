import TheActualInternalStageCostsItsSizeMinusOnePossibleEdge
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
def deleteInsideIso {X:Type u} (G:SimpleGraph X) (A:Set X) (I:Set A) :
    (G.induce A).induce Iᶜ ≃g G.induce (A\(Subtype.val '' I)) where
  toFun x := ⟨x.val.val,x.val.property,by rintro ⟨v,hv,e⟩;exact x.property ((Subtype.ext e : v=x.val) ▸ hv)⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,fun m => x.property.2 ⟨_,m,rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

namespace TenPortSupport
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)
def spent (I:Set W.available) (V:Set ↥(W.supportᶜ:Set X)) := W.innerCut I∪(Subtype.val '' V)

noncomputable def after_port_cuts (I:Set W.available) (V:Set ↥(W.supportᶜ:Set X)) :
    ((G.induce W.available).induce Iᶜ⊕g W.outside.induce Vᶜ) ≃g G.induce (W.spent I V)ᶜ := by
  let A := W.available\(Subtype.val '' I)
  let O := W.supportᶜ\(Subtype.val '' V)
  have cover : A∪O=(W.spent I V)ᶜ := by
    ext x
    change ((x∈W.support ∧ x∉W.innerTips) ∧ x∉Subtype.val '' I) ∨
      (x∉W.support ∧ x∉Subtype.val '' V) ↔ ¬((x∈W.innerTips ∨ x∈Subtype.val '' I) ∨ x∈Subtype.val '' V)
    have z : x∈W.innerTips → x∈W.support := fun m => m.1
    have left : x∈Subtype.val '' I → x∈W.support := by rintro ⟨v,_,rfl⟩;exact v.property.1
    have right : x∈Subtype.val '' V → x∉W.support := by rintro ⟨v,_,rfl⟩;exact v.property
    tauto
  have sep : Disjoint A O := Set.disjoint_left.mpr (fun _ a o => o.1 a.1.1)
  have none : ∀x∈A,∀y∈O,¬G.Adj x y := fun x hx y hy adj => hy.1 (W.ordinary_neighbors_stay hx.1.1 hx.1.2 adj)
  exact (Iso.sumCongr (deleteInsideIso G W.available I) (deleteInsideIso G W.supportᶜ V)).trans
    (regionSumIso G _ A O cover sep none)

theorem paid_cut_exposure (I:Set W.available) (V:Set ↥(W.supportᶜ:Set X)) (D:ℕ) :
    minimumExposure (W.outside.induce Vᶜ) D≤minimumExposure (G.induce (W.spent I V)ᶜ) D := by
  rw [←minimumExposure_iso (W.after_port_cuts I V) D,minimumExposure_sumGraph];omega

#print axioms after_port_cuts
#print axioms paid_cut_exposure
end TenPortSupport
#print axioms deleteInsideIso
end JSP452Audit.StarHost
