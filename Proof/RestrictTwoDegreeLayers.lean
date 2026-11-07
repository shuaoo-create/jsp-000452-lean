import GeneralPairLayerParity
namespace JSP452Audit.StarHost
open SimpleGraph
namespace TwoDegreeLayers

theorem neighbor_sum_of_partition {X:Type*} [Finite X] {m:ℕ} (G:SimpleGraph X) (P:Fin m→SimpleGraph X)
    (sub:∀i,P i≤G) (cover:∀x y,G.Adj x y → ∃i,(P i).Adj x y)
    (unique:∀i j x y,(P i).Adj x y → (P j).Adj x y → i=j) (v:X) :
    (∑i:Fin m,((P i).neighborSet v).ncard)=(G.neighborSet v).ncard := by
  classical
  let f (a:(i:Fin m) × ((P i).neighborSet v)) : G.neighborSet v := ⟨a.2.val,sub a.1 a.2.property⟩
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ eq
    have same : x.val=y.val := congrArg Subtype.val eq
    have ij := unique i j v x.val x.property (same ▸ y.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext same)
  have onto : Function.Surjective f := by
    intro x;obtain ⟨i,e⟩ := cover v x.val x.property
    exact ⟨⟨i,⟨x.val,e⟩⟩,rfl⟩
  have eq := Nat.card_congr (Equiv.ofBijective f ⟨inj,onto⟩)
  rwa [Nat.card_sigma] at eq

noncomputable def restrict {X Y:Type*} [Finite X] [Finite Y] {H:SimpleGraph Y} {m:ℕ}
    (V:TwoDegreeLayers H m) (f:X↪Y) : TwoDegreeLayers (H.comap f) m := by
  let P := fun i => (V.part i).comap f
  have sub (i) : P i≤H.comap f := fun _ _ e => V.sub i e
  have cover (x y:X) (e:(H.comap f).Adj x y) : ∃i,(P i).Adj x y := V.cover (f x) (f y) e
  have unique (i j) (x y:X) (a:(P i).Adj x y) (b:(P j).Adj x y) := V.unique i j (f x) (f y) a b
  refine ⟨P,sub,cover,unique,?_,neighbor_sum_of_partition _ _ sub cover unique⟩
  intro i v
  let g (x:(P i).neighborSet v) : (V.part i).neighborSet (f v) := ⟨f x.val,x.property⟩
  exact (Nat.card_le_card_of_injective g (fun _ _ eq => Subtype.ext (f.injective (congrArg Subtype.val eq)))).trans (V.cap i (f v))

theorem restrict_part {X Y:Type*} [Finite X] [Finite Y] {H:SimpleGraph Y} {m:ℕ}
    (V:TwoDegreeLayers H m) (f:X↪Y) (i:Fin m) : (V.restrict f).part i=(V.part i).comap f := rfl

#print axioms neighbor_sum_of_partition
#print axioms restrict
#print axioms restrict_part
end TwoDegreeLayers
end JSP452Audit.StarHost
