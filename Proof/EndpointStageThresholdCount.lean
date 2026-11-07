import ForestMatchingEndpointHalfOrder
import HighStarCover
namespace JSP452Audit.StarHost
open SimpleGraph

theorem endpoint_threshold_stage {X : Type*} [Finite X] {s q p : ℕ} (G : SimpleGraph X)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (endpt : ForestMatchingEndpoint G n q) (hq : 0<q)
    (T : Set X) (cap : ∀v:↥(Tᶜ : Set X),Nat.card ((G.induce Tᶜ).neighborSet v)≤p)
    (pos : 0<originalThresholdCount n (p+1)) :
    q-1+originalThresholdCount n (p+1)≤T.ncard := by
  classical
  let k := min (q-1) T.ncard
  obtain ⟨A,sub,num⟩ := Set.exists_subset_card_eq (show k≤T.ncard from Nat.min_le_right _ _)
  have small : A.ncard<q := by have := Nat.min_le_left (q-1) T.ncard;dsimp [k] at num;omega
  have copy := endpoint_survives_cover G n pn endpt A small
  let V : Set ↥(Aᶜ : Set X) := {v | v.val∈T}
  have image : Subtype.val '' V=T\A := by
    ext v
    constructor
    · rintro ⟨x,h,rfl⟩;exact ⟨h,x.property⟩
    · rintro ⟨h,away⟩;exact ⟨⟨v,away⟩,h,rfl⟩
  have card : V.ncard=(T\A).ncard := by rw [←image,Set.ncard_image_of_injective _ Subtype.val_injective]
  have hits (f : (oneStar (p+1)).Copy (G.induce Aᶜ)) : ∃x,f x∈V := by
    by_contra! miss
    let send (x:Vertices (fun _:Fin 1 => p+1)) : ↥(Tᶜ : Set X) := ⟨(f x).val,miss x⟩
    have lift : (oneStar (p+1)).IsContained (G.induce Tᶜ) := by
      refine ⟨{toHom := {toFun := send,map_rel' := fun e => f.toHom.map_rel' e},injective' := ?_}⟩
      exact fun _ _ eq => f.injective (Subtype.ext (congrArg (fun v:↥(Tᶜ : Set X) => v.val) eq))
    obtain ⟨v,large⟩ := high_degree_of_star lift
    have limit := cap v
    omega
  have bound := count_large_of_hits (G.induce Aᶜ) V p n hits copy
  change originalThresholdCount n (p+1)≤V.ncard at bound
  have total := Set.ncard_sdiff_add_ncard_of_subset sub
  dsimp [k] at num
  omega

#print axioms endpoint_threshold_stage
end JSP452Audit.StarHost
