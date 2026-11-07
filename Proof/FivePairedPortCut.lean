import FiveDegreeDoubleWidth
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Two ports and three new vertices. Each port joins all three new vertices,
the latter form a triangle, and the two ports have no internal edge. -/
def two_port_piece (U : Type*) : SimpleGraph (U⊕Fin 3) where
  Adj
    | .inl _,.inl _ => False
    | .inl _,.inr _ | .inr _,.inl _ => True
    | .inr x,.inr y => x≠y
  symm := by
    constructor
    rintro (a|a) (b|b) h
    · exact h
    · trivial
    · trivial
    · exact Ne.symm h
  loopless := by
    constructor
    rintro (a|a) h
    · exact h
    · exact h rfl

theorem two_port_piece_label_degree {U : Type*} [Finite U] (u:U) :
    Nat.card ((two_port_piece U).neighborSet (.inl u))=3 := by
  let f := (Function.Embedding.inr : Fin 3 ↪ U⊕Fin 3)
  have eq : (two_port_piece U).neighborSet (.inl u)=Set.range f := by
    ext v;cases v <;> simp [two_port_piece,f,SimpleGraph.mem_neighborSet]
  rw [Nat.card_coe_set_eq,eq,Set.ncard_range_of_injective f.injective,Nat.card_fin]

theorem two_port_piece_internal_degree {U : Type*} [Finite U] (two : Nat.card U=2) (z:Fin 3) :
    Nat.card ((two_port_piece U).neighborSet (.inr z))=4 := by
  have eq : (two_port_piece U).neighborSet (.inr z)=(Set.univ : Set (U⊕Fin 3))\{.inr z} := by
    ext v;cases v <;> simp [two_port_piece,SimpleGraph.mem_neighborSet,ne_comm]
  have rm := Set.ncard_sdiff_singleton_add_one (Set.mem_univ (Sum.inr z : U⊕Fin 3))
  rw [Set.ncard_univ,Nat.card_sum,two,Nat.card_fin] at rm
  rw [Nat.card_coe_set_eq,eq];omega

namespace FiveExposurePorts
variable {X : Type*} [Finite X] {G : SimpleGraph X} (s : FiveExposurePorts G)
variable {Z : Type*} [Finite Z]

def addedSet : Set (X⊕(s.U⊕Z)) := Set.range Sum.inr

/-- Count every red port edge exactly once in the cut of the actual auxiliary
simple graph. Distinct ports may still share an old endpoint. -/
theorem red_port_cross_count (J : SimpleGraph (s.U⊕Z)) (R : SimpleGraph (X⊕(s.U⊕Z))) (sub : R≤s.auxiliary J) :
    crossCount R s.addedSet s.addedSetᶜ=(s.marked R)ᶜ.ncard := by
  classical
  let K := s.addedSet (Z:=Z)
  let T := (s.marked R)ᶜ
  let Ed := {p : (↥K × ↥(Kᶜ : Set (X⊕(s.U⊕Z)))) // R.Adj p.1.val p.2.val}
  let f (u : T) : Ed := ⟨(⟨.inr (.inl u.val),⟨_,rfl⟩⟩,⟨.inl (s.target u.val),by rintro ⟨v,h⟩;cases h⟩),
    (Classical.not_not.mp u.property).symm⟩
  have inj : Function.Injective f := by
    intro a b eq
    have h : (Sum.inr (Sum.inl a.val) : X⊕(s.U⊕Z))= .inr (.inl b.val) :=
      congrArg (fun z:Ed => z.val.1.val) eq
    exact Subtype.ext (Sum.inl.inj (Sum.inr.inj h))
  have sur : Function.Surjective f := by
    rintro ⟨⟨⟨v,hv⟩,⟨w,hw⟩⟩,edge⟩
    rcases hv with ⟨v,rfl⟩
    rcases w with x|bad
    · rcases v with u|z
      · have eq : s.target u=x := sub edge
        subst x
        refine ⟨⟨u,fun out => out edge.symm⟩,?_⟩
        rfl
      · exact (show False from sub edge).elim
    · exact (hw ⟨bad,rfl⟩).elim
  change Nat.card Ed=T.ncard
  rw [←Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective f ⟨inj,sur⟩).symm

end FiveExposurePorts
#print axioms two_port_piece_label_degree
#print axioms two_port_piece_internal_degree
#print axioms FiveExposurePorts.red_port_cross_count
end JSP452Audit.StarHost
