import DoubleEscapePeakFactorFrontier
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def cutPieceSet {X : Type u} (G : SimpleGraph X) (A : Set X) (C : (G.induce Aᶜ).ConnectedComponent) : Set X :=
  Subtype.val '' C.supp

noncomputable def cutPieceVertexEquiv {X : Type u} (G : SimpleGraph X) (A : Set X)
    (C : (G.induce Aᶜ).ConnectedComponent) : C.supp ≃ ↥(cutPieceSet G A C) :=
  Equiv.Set.imageOfInjOn Subtype.val C.supp Subtype.val_injective.injOn

theorem cut_piece_outside {X : Type u} (G : SimpleGraph X) (A : Set X) (C : (G.induce Aᶜ).ConnectedComponent) :
    cutPieceSet G A C⊆Aᶜ := by rintro _ ⟨x,_,rfl⟩;exact x.property

theorem cut_piece_neighbor {X : Type u} (G : SimpleGraph X) (A : Set X) (C : (G.induce Aᶜ).ConnectedComponent)
    {x y:X} (inside : x∈cutPieceSet G A C) (edge : G.Adj x y) (out : y∉A) : y∈cutPieceSet G A C := by
  obtain ⟨z,mem,rfl⟩ := inside
  let w : ↥(Aᶜ : Set X) := ⟨y,out⟩
  have adj : (G.induce Aᶜ).Adj z w := edge
  exact ⟨w,(C.mem_supp_congr_adj adj).mp mem,rfl⟩

theorem total_cut_piece_boundaries {X : Type u} [Finite X] (G : SimpleGraph X) (A : Set X)
    [Fintype (G.induce Aᶜ).ConnectedComponent] :
    (∑C:(G.induce Aᶜ).ConnectedComponent,crossCount G (cutPieceSet G A C) A)=crossCount G Aᶜ A := by
  classical
  let _ := Fintype.ofFinite X
  let H := G.induce Aᶜ
  let f (z:↥(Aᶜ : Set X)) := (G.neighborSet z.val∩A).ncard
  have single (C:H.ConnectedComponent) : crossCount G (cutPieceSet G A C) A=∑z:C.supp,f z.val := by
    rw [crossCount_eq_neighbor_sum]
    exact (Fintype.sum_equiv (cutPieceVertexEquiv G A C) (fun z:C.supp => f z.val)
      (fun z:↥(cutPieceSet G A C) => (G.neighborSet z.val∩A).ncard) (fun _ => rfl)).symm
  change (∑C:H.ConnectedComponent,crossCount G (cutPieceSet G A C) A)=crossCount G Aᶜ A
  simp_rw [single]
  let e := Equiv.sigmaFiberEquiv H.connectedComponentMk
  have total := Fintype.sum_equiv e (fun v => f v.2.val) f (fun _ => rfl)
  rw [Fintype.sum_sigma] at total
  calc
    _ = ∑c:H.ConnectedComponent,∑y:{x // H.connectedComponentMk x=c},f y.val := by
      apply Finset.sum_congr rfl
      intro c _
      exact Fintype.sum_equiv (show ↥c.supp ≃ {x // H.connectedComponentMk x=c} from Equiv.refl _)
        (fun z:↥c.supp => f z.val) (fun y:{x // H.connectedComponentMk x=c} => f y.val) (fun _ => rfl)
    _ = _ := total.trans (crossCount_eq_neighbor_sum G Aᶜ A).symm

#print axioms cut_piece_outside
#print axioms cut_piece_neighbor
#print axioms total_cut_piece_boundaries
end JSP452Audit.StarHost