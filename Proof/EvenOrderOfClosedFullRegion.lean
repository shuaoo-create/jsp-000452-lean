import SaturatedOriginalCutVertices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem even_order_of_closed_full_region {X:Type u} [Finite X] (G:SimpleGraph X) (D:ℕ)
    (empty:(oddRegularComponents G D).ncard=0) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (full:∀x∈U,Nat.card (G.neighborSet x)=D) :
    Even U.ncard := by
  classical
  let B := {c:G.ConnectedComponent|c.supp⊆U}
  let _ := Fintype.ofFinite B
  let _ (c:↥B) := Fintype.ofFinite ↥c.val.supp
  have even (c:↥B) : Even (Nat.card c.val.supp) := by
    by_contra no
    have mem : c.val∈oddRegularComponents G D := ⟨Nat.not_even_iff_odd.mp no,fun x hx => full x (c.property hx)⟩
    have pos := (Set.ncard_pos (Set.toFinite _)).mpr (show (oddRegularComponents G D).Nonempty from ⟨c.val,mem⟩)
    omega
  let f (z:(c:↥B) × c.val.supp) : U := ⟨z.2.val,z.1.property z.2.property⟩
  have inj : Function.Injective f := by
    rintro ⟨c,x⟩ ⟨d,y⟩ eq
    have same : x.val=y.val := congrArg (fun z:U => z.val) eq
    have cd : c=d := Subtype.ext ((show G.connectedComponentMk x.val=c.val from x.property).symm.trans
      ((congrArg G.connectedComponentMk same).trans (show G.connectedComponentMk y.val=d.val from y.property)))
    subst d
    exact congrArg (Sigma.mk c) (Subtype.ext same)
  have onto : Function.Surjective f := by
    intro x
    have inc := cubic_closed_component G U x.val x.property closed
    exact ⟨⟨⟨G.connectedComponentMk x.val,inc⟩,⟨x.val,rfl⟩⟩,rfl⟩
  have size := (Nat.card_congr (Equiv.ofBijective f ⟨inj,onto⟩)).symm
  rw [Nat.card_sigma] at size
  choose k hk using even
  refine ⟨∑c:↥B,k c,?_⟩
  rw [←Finset.sum_add_distrib]
  exact size.trans (Finset.sum_congr rfl (fun c _ => hk c))

#print axioms even_order_of_closed_full_region
end JSP452Audit.StarHost
