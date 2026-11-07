import SuppressedCoreExteriorFloor
namespace JSP452Audit.StarHost
open SimpleGraph

theorem forced_host_of_copy {X Y I J : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (embed : G.Copy H) (A : SimpleGraph I) (B : SimpleGraph J) (source : Forces G A B) : Forces H A B := by
  intro R _
  let P := G⊓R.comap embed
  have sub : P≤G := inf_le_left
  let red : P.Copy R := { toHom := {toFun := embed, map_rel' := fun e => e.2}, injective' := embed.injective }
  let blue : (G \ P).Copy (H \ R) := {
    toHom := { toFun := embed,map_rel' := fun e => ⟨embed.toHom.map_adj e.1,fun h => e.2 ⟨e.1,h⟩⟩ }
    injective' := embed.injective }
  rcases source P sub with ar|br
  · exact Or.inl (ar.trans ⟨red⟩)
  · exact Or.inr (br.trans ⟨blue⟩)

theorem uniform_envelope_host_copy {X Y : Type*} [Finite X] [Finite Y] {G : SimpleGraph X} {H : SimpleGraph Y}
    (embed : G.Copy H) (j : ℕ) : uniformEnvelope G j≤uniformEnvelope H j := by
  by_cases present : 0<uniformEnvelope G j
  · obtain ⟨a,b,p,q,pa,pb,pp,pq,hgt,wide,forced⟩ := uniformEnvelope_attained G j present
    exact wide ▸ uniform_pair_le_envelope H a b p q j pa pb pp pq hgt (forced_host_of_copy embed _ _ forced)
  · omega

theorem exterior_envelope_in_erased {X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ} (K : DegreeRegion G D)
    (j : ℕ) : uniformEnvelope (G.induce K.rest) j≤uniformEnvelope (eraseInternal G K.core) j := by
  have apart := (core_rest_partition G K.barrier K.pieces).2.1
  let e : (G.induce K.rest).Copy (eraseInternal G K.core) := {
    toHom := {toFun := Subtype.val,map_rel' := fun {x _} adj =>
      ⟨adj,fun both => Set.disjoint_left.mp apart both.1 x.property⟩}
    injective' := Subtype.val_injective }
  exact uniform_envelope_host_copy e j

#print axioms forced_host_of_copy
#print axioms uniform_envelope_host_copy
#print axioms exterior_envelope_in_erased
end JSP452Audit.StarHost