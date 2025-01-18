import Mathlib

section corner

variable {R : Type*} (e : R)

namespace Subsemigroup

variable [Semigroup R]

/-- The corner associated to an element `e` in a semigroup
is the subsemigroup of all elements of the form `e * r * e`. -/
def corner : Subsemigroup R where
  carrier := Set.range (e * · * e)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * e * e * b, by simp_rw [mul_assoc]⟩

variable {e} (idem : IsIdempotentElem e)
include idem

lemma mem_corner_iff {r : R} : r ∈ corner e ↔ e * r = r ∧ r * e = r :=
  ⟨by rintro ⟨r, rfl⟩; simp_rw [← mul_assoc, idem.eq, mul_assoc, idem.eq, true_and],
    (⟨r, by simp_rw [·]⟩)⟩

lemma mem_corner_iff_mul_left (hc : IsMulCentral e) {r : R} : r ∈ corner e ↔ e * r = r := by
  rw [mem_corner_iff idem, and_iff_left_of_imp]; intro; rwa [← hc.comm]

lemma mem_corner_iff_mul_right (hc : IsMulCentral e) {r : R} : r ∈ corner e ↔ r * e = r := by
  rw [mem_corner_iff_mul_left idem hc, hc.comm]

lemma mem_corner_iff_mem_range_mul_left (hc : IsMulCentral e) {r : R} :
    r ∈ corner e ↔ r ∈ Set.range (e * ·) := by
  simp_rw [corner, mem_mk, Set.mem_range, ← hc.comm, ← mul_assoc, idem.eq]

lemma mem_corner_iff_mem_range_mul_right (hc : IsMulCentral e) {r : R} :
    r ∈ corner e ↔ r ∈ Set.range (· * e) := by
  simp_rw [mem_corner_iff_mem_range_mul_left idem hc, hc.comm]

/-- The corner associated to an idempotent `e` in a semiring without 1
is the semiring with `e` as 1 consisting of all element of the form `e * r * e`. -/
@[nolint unusedArguments]
def _root_.IsIdempotentElem.Corner (_ : IsIdempotentElem e) : Type _ := Subsemigroup.corner e

end Subsemigroup

/-- The corner associated to an element `e` in a semiring without 1
is the subsemiring without 1 of all elements of the form `e * r * e`. -/
def NonUnitalSubsemiring.corner [NonUnitalSemiring R] : NonUnitalSubsemiring R where
  __ := Subsemigroup.corner e
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by simp_rw [mul_add, add_mul]⟩
  zero_mem' := ⟨0, by simp_rw [mul_zero, zero_mul]⟩

/-- The corner associated to an element `e` in a ring without `
is the subring without 1 of all elements of the form `e * r * e`. -/
def NonUnitalRing.corner [NonUnitalRing R] : NonUnitalSubring R where
  __ := NonUnitalSubsemiring.corner e
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, by simp_rw [mul_neg, neg_mul]⟩

instance [NonUnitalSemiring R] (idem : IsIdempotentElem e) : Semiring idem.Corner where
  __ : NonUnitalSemiring (NonUnitalSubsemiring.corner e) := inferInstance
  one := ⟨e, e, by simp_rw [idem.eq]⟩
  one_mul r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).1
  mul_one r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).2

instance [NonUnitalCommSemiring R] (idem : IsIdempotentElem e) : CommSemiring idem.Corner where
  __ : NonUnitalCommSemiring (NonUnitalSubsemiring.corner e) := inferInstance
  __ : Semiring idem.Corner := inferInstance

instance [NonUnitalRing R] (idem : IsIdempotentElem e) : Ring idem.Corner where
  __ : NonUnitalRing (NonUnitalRing.corner e) := inferInstance
  __ : Semiring idem.Corner := inferInstance

instance [NonUnitalCommRing R] (idem : IsIdempotentElem e) : CommRing idem.Corner where
  __ : NonUnitalCommRing (NonUnitalRing.corner e) := inferInstance
  __ : Semiring idem.Corner := inferInstance

variable {I : Type*} [Fintype I] {e : I → R}

/-- A complete orthogonal family of central idempotents in a semiring
give rise to a direct product decomposition. -/
def CompleteOrthogonalIdempotents.mulEquivOfIsMulCentral [Ring R]
    (he : CompleteOrthogonalIdempotents e) (hc : ∀ i, IsMulCentral (e i)) :
    R ≃+* Π i, (he.idem i).Corner where
  toFun r i := ⟨_, r, rfl⟩
  invFun r := ∑ i, (r i).1
  left_inv r := by
    simp_rw [(hc _).comm, mul_assoc, (he.idem _).eq, ← Finset.mul_sum, he.complete, mul_one]
  right_inv r := funext fun i ↦ Subtype.ext <| by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single i _ (by simp at ·)]
    · have ⟨r', eq⟩ := (r i).2
      rw [← eq]; simp_rw [← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem i).eq]
    · intro j _ ne; have ⟨r', eq⟩ := (r j).2
      rw [← eq]; simp_rw [← mul_assoc, he.ortho ne.symm, zero_mul]
  map_mul' r₁ r₂ := funext fun i ↦ Subtype.ext <|
    calc e i * (r₁ * r₂) * e i
     _ = e i * (r₁ * e i * r₂) * e i := by simp_rw [← (hc i).comm r₁, ← mul_assoc, (he.idem i).eq]
     _ = e i * r₁ * e i * (e i * r₂ * e i) := by
      conv in (r₁ * _ * r₂) => rw [← (he.idem i).eq]
      simp_rw [mul_assoc]
  map_add' r₁ r₂ := funext fun i ↦ Subtype.ext <| by simpa [mul_add] using add_mul ..

/-- A complete orthogonal family of idempotents in a commutative semiring
give rise to a direct product decomposition. -/
def CompleteOrthogonalIdempotents.mulEquivOfComm [CommRing R]
    (he : CompleteOrthogonalIdempotents e) : R ≃+* Π i, (he.idem i).Corner :=
  he.mulEquivOfIsMulCentral fun _ ↦ Semigroup.mem_center_iff.mpr fun _ ↦ mul_comm ..

end corner

section

open TensorProduct

section Morita

universe u₁ u₂ u₃

open CategoryTheory

open Function MulOpposite Set
open scoped Pointwise

/--
Two rings are Morita equivalent if their module categories are equivalent.
-/
structure IsMoritaEquivalent (R : Type u₁) [Ring R] (S : Type u₂) [Ring S] : Prop where
  cond : Nonempty <| ModuleCat.{max u₁ u₂} R ≌ ModuleCat.{max u₁ u₂} S

namespace IsMoritaEquivalent

variable {R : Type u₁} [Ring R] {S : Type u₂} [Ring S] {T : Type u₃} [Ring T]

lemma refl : IsMoritaEquivalent R R where
  cond := ⟨.refl⟩

lemma symm (h : IsMoritaEquivalent R S) : IsMoritaEquivalent S R where
  cond := h.cond.map .symm

theorem ofRingEquiv (e : R ≃+* S): IsMoritaEquivalent R S := sorry

lemma morita_iff (e' : R): IsMoritaEquivalent R S ↔ ∃(n : ℕ),
    ∃(e : R)(he : IsIdempotentElem e)(he' : Doset.doset e ⊤ ⊤ = ⊤),
    Nonempty <| S ≃+* he.Corner := by
  sorry

end IsMoritaEquivalent

end Morita

section brauer

universe u v

variable (K : Type u) [Field K]

structure CSA (K : Type u) [Field K] where
  (carrier : Type v)
  [ring : Ring carrier]
  [algebra : Algebra K carrier]
  [isCentral : Algebra.IsCentral K carrier]
  [isSimple : IsSimpleRing carrier]
  [fin_dim : FiniteDimensional K carrier]

instance : CoeSort (CSA.{u, v} K) (Type v) where
  coe A := A.carrier

instance (A : CSA K) : Ring A := A.ring

instance (A : CSA K) : Algebra K A := A.algebra

instance (A : CSA K) : Algebra.IsCentral K A := A.isCentral

instance (A : CSA K) : IsSimpleRing A := A.isSimple

instance (A : CSA K) : FiniteDimensional K A := A.fin_dim

variable {K : Type u} [Field K]

structure BrauerEquivalence (A B : CSA K) where
(n m : ℕ) [hn: NeZero n] [hm : NeZero m]
(iso: Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)

instance (A B : CSA K) (h : BrauerEquivalence A B) : NeZero h.n := h.hn
instance (A B : CSA K) (h : BrauerEquivalence A B) : NeZero h.m := h.hm

abbrev IsBrauerEquivalent (A B : CSA K) := Nonempty (BrauerEquivalence A B)

end brauer

universe u v

variable (K : Type u) [Field K]

lemma IsSimpleRing.left_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleRing (B ⊗[K] C)] :
    IsSimpleRing B := sorry

lemma IsSimpleRing.right_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleRing (B ⊗[K] C)] :
    IsSimpleRing C := sorry

instance TensorProduct.simple (B C : Type*) [Ring B] [Ring C] [Algebra K C]
  [Algebra K B] [IsSimpleRing B] [IsSimpleRing C] [Algebra.IsCentral K B]:
  IsSimpleRing (B ⊗[K] C) := sorry

lemma center_tensorProduct
    (B C : Type*) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K (B ⊗[K] C) =
      (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range := by sorry

lemma TwoSidedIdeal.comap_comap
    {R S T : Type*} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (I : TwoSidedIdeal T) :
  TwoSidedIdeal.comap f (TwoSidedIdeal.comap g I) = TwoSidedIdeal.comap (g.comp f) I := rfl

open TwoSidedIdeal in
@[simp]
def TwoSidedIdeal.orderIsoOfRingEquiv {R R' : Type*} [Ring R] [Ring R']
  {F : Type*} [EquivLike F R R'] [RingEquivClass F R R'] (f : F) :
    TwoSidedIdeal R ≃o TwoSidedIdeal R' where
  toFun := comap (RingEquivClass.toRingEquiv f).symm
  invFun := comap (RingEquivClass.toRingEquiv f)
  left_inv I := by
    have :=
      comap_comap (R := R) (S := R') (RingEquivClass.toRingEquiv f)
      (RingEquivClass.toRingEquiv f).symm I
    simp at this
    erw [TwoSidedIdeal.comap_comap (RingEquivClass.toRingEquiv f).toRingHom
      (RingEquivClass.toRingEquiv f).symm.toRingHom]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp]
    rfl
  right_inv := fun I => SetLike.ext <| fun x => by
    simp only [mem_comap, RingEquiv.apply_symm_apply]
  map_rel_iff' := by
    intro I J
    rw [le_iff, le_iff]
    constructor
    · rintro h x hx

      specialize @h (RingEquivClass.toRingEquiv f x) (by simpa [TwoSidedIdeal.mem_comap])
      simpa [TwoSidedIdeal.mem_comap] using h
    · intro h x hx
      simp only [Equiv.coe_fn_mk, SetLike.mem_coe, mem_comap] at hx ⊢
      exact h hx

lemma TensorProduct.flip_mk_injective {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [NoZeroSMulDivisors R N] [Module.Flat R M] (a : N) (ha : a ≠ 0) :
    Function.Injective ((TensorProduct.mk R M N).flip a) := by
  intro x y e
  -- simp only [LinearMap.flip_apply, mk_apply] at e
  apply (TensorProduct.rid R M).symm.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := M) (LinearMap.toSpanSingleton R N a)
    (smul_left_injective R ha)
  simpa using e

lemma IsCentral.left_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Nontrivial B] [Nontrivial C] [Algebra K C] [Algebra K B]
    [FiniteDimensional K B] [hbc : Algebra.IsCentral K (B ⊗[K] C)] :
    Algebra.IsCentral K B := by
  letI : Nontrivial (B ⊗[K] C) := Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  have h := (Subalgebra.equivOfEq (R := K) (A := B ⊗[K] C) _ _ <|
    hbc.center_eq_bot K (B ⊗[K] C)) |>.trans <| Algebra.botEquiv K (B ⊗[K] C)
  have : (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range ≤
    Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
    simp only [AlgHom.mem_range, AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Subtype.exists, exists_prop] at hx
    obtain ⟨b, hb0, hb⟩ := hx
    rw [Subalgebra.mem_center_iff] at hb0 ⊢
    intro bc
    induction bc using TensorProduct.induction_on with
    | zero => simp
    | tmul b' c =>
      subst hb
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      congr 1
      exact hb0 b'
    | add _ _ _ _ => simp_all [add_mul, mul_add]
  have eq: (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range =
      (⊥ : Subalgebra K (B ⊗[K] C)) := by
    refine le_antisymm ?_ <| OrderBot.bot_le _
    rw [← hbc.center_eq_bot]; exact this
  let f : Subalgebra.center K B →ₐ[K] ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range := {
      toFun := fun ⟨b, hb⟩ ↦ ⟨b ⊗ₜ 1, ⟨⟨b, hb⟩, rfl⟩⟩
      map_one' := by simp; rfl
      map_mul' := fun _ _ ↦ by ext : 1; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp [add_tmul]
      commutes' := fun _ ↦ rfl}
  have f_surj : Function.Surjective f := fun ⟨bc, ⟨⟨b, hb⟩, h⟩⟩ ↦ ⟨⟨b, hb⟩, by
    simp [f]
    change _ ⊗ₜ _ = _ at h
    simp only [RingHom.coe_coe, Subalgebra.coe_val] at h⊢
    exact h⟩

  have e : ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range ≃ₐ[K] (Subalgebra.center K B) :=
    (AlgEquiv.ofBijective f
    ⟨fun ⟨b1, hb1⟩ ⟨b2, hb2⟩ h12 ↦ by
      simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Subtype.mk.injEq, f] at h12
      ext ; simp only [f]
      exact TensorProduct.flip_mk_injective _ one_ne_zero h12,
    f_surj⟩).symm
  have e2 := Subalgebra.equivOfEq _ _ eq |>.trans <| Algebra.botEquiv K _
  have ee: Subalgebra.center K B ≃ₐ[K] K := e.symm.trans e2
  exact ⟨le_of_eq <| Subalgebra.eq_of_le_of_finrank_eq (OrderBot.bot_le _)
    (by rw [ee.toLinearEquiv.finrank_eq, Subalgebra.finrank_bot, Module.finrank_self])|>.symm⟩

lemma IsSimpleRing.ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (hA : IsSimpleRing A) : IsSimpleRing B :=
  ⟨OrderIso.isSimpleOrder_iff (TwoSidedIdeal.orderIsoOfRingEquiv e.toRingEquiv)|>.1 hA.1⟩

lemma bijective_of_dim_eq_of_isCentralSimple
    (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] [csa_source : IsSimpleRing A]
    [fin_source : FiniteDimensional K A]
    [fin_target : FiniteDimensional K B]
    (f : A →ₐ[K] B) (h : Module.finrank K A = Module.finrank K B) :
    Function.Bijective f := by
  obtain hA|hA := subsingleton_or_nontrivial A
  · have eq1 : Module.finrank K A = 0 := by
      rw [finrank_zero_iff_forall_zero]
      intro x
      apply Subsingleton.elim
    rw [eq1] at h
    replace h : Subsingleton B := by
      constructor
      symm at h
      rw [finrank_zero_iff_forall_zero] at h
      intro a b
      rw [h a, h b]
    rw [Function.bijective_iff_existsUnique]
    intro b
    refine ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  sorry
  -- · have := IsSimpleRing.iff_injective_ringHom_or_subsingleton_codomain A |>.1 csa_source
  --     f.toRingHom
  --   rcases this with (H|H)
  --   · refine ⟨H, ?_⟩
  --     change Function.Surjective f.toLinearMap
  --     have := f.toLinearMap.finrank_range_add_finrank_ker
  --     rw [show Module.finrank K (LinearMap.ker f.toLinearMap) = 0 by
  --       rw [finrank_zero_iff_forall_zero]
  --       rintro ⟨x, hx⟩
  --       rw [LinearMap.ker_eq_bot (f := f.toLinearMap) |>.2 H] at hx
  --       ext
  --       exact hx, add_zero, h] at this
  --     rw [← LinearMap.range_eq_top]

  --     apply Submodule.eq_top_of_finrank_eq
  --     exact this
  --   · have : (1 : A) ∈ TwoSidedIdeal.ker f.toRingHom := by
  --       simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, RingHom.coe_coe, map_one]
  --       exact Subsingleton.elim _ _
  --     simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, map_one] at this
  --     have hmm : Nontrivial B := by
  --       let e := LinearEquiv.ofFinrankEq _ _ h
  --       exact Equiv.nontrivial e.symm.toEquiv

  --     exact one_ne_zero this |>.elim
lemma dim_eq (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
  rw [Module.finrank_tensorProduct]
  rw [show Module.finrank K (Module.End K A) =
    Module.finrank K (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) from
    (algEquivMatrix <| Module.finBasis _ _).toLinearEquiv.finrank_eq]
  rw [Module.finrank_matrix, Fintype.card_fin]
  rw [show Module.finrank K Aᵐᵒᵖ = Module.finrank K A from
    (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).symm.finrank_eq]
  simp only [Module.finrank_self, mul_one]

noncomputable def equivEnd (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A]: A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (AlgHom.tensorMopToEnd K A) <| sorry
  -- bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <|
  --   dim_eq K A
end

section Field

variable (F A B : Type*) [Field F] [Ring A] [Ring B] [Algebra F A] [Algebra F B]

open TensorProduct

lemma Algebra.IsCentral_ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (hA : Algebra.IsCentral F A):  Algebra.IsCentral F B where
  out x hx := by
    obtain ⟨k, hk⟩ := hA.1 (show e.symm x ∈ _ by
      simp only [Subalgebra.mem_center_iff] at hx ⊢
      exact fun x => by simpa using congr(e.symm $(hx (e x))))
    exact ⟨k, by apply_fun e.symm; rw [← hk]; simp [ofId_apply]⟩

instance [IsSimpleRing A]: IsSimpleRing Aᵐᵒᵖ := sorry

theorem IsAzumaya_iff_CentralSimple [Nontrivial A]: IsAzumaya F A ↔ FiniteDimensional F A ∧
    Algebra.IsCentral F A ∧ IsSimpleRing A :=
  ⟨fun ⟨bij⟩ ↦
    letI e := AlgEquiv.ofBijective _ bij|>.trans <| algEquivMatrix <| Module.finBasis _ _
    letI : Nonempty (Fin (Module.finrank F A)) := ⟨⟨_, Module.finrank_pos⟩⟩
    ⟨IsAzumaya.toFinite, ⟨by
    have : Algebra.IsCentral F (A ⊗[F] Aᵐᵒᵖ) :=
      Algebra.IsCentral_ofAlgEquiv F _ _ e.symm <| Algebra.IsCentral.matrix F F
        (Fin (Module.finrank F A))
    exact IsCentral.left_of_tensor F A Aᵐᵒᵖ, by
    haveI := IsSimpleRing.matrix (Fin (Module.finrank F A)) F
    have sim : IsSimpleRing (A ⊗[F] Aᵐᵒᵖ) := IsSimpleRing.ofAlgEquiv F _ _ e.symm this
    exact IsSimpleRing.left_of_tensor F A Aᵐᵒᵖ⟩⟩,
    fun ⟨fin, cen, sim⟩ ↦ {
      out := Module.Projective.out
      eq_of_smul_eq_smul {k1} {k2} ha := by
        specialize ha (1 : A)
        rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at ha
        exact NoZeroSMulDivisors.algebraMap_injective _ _ ha
      fg_top := fin.1
      bij := bijective_of_dim_eq_of_isCentralSimple F _ _
        (AlgHom.tensorMopToEnd F A) <| dim_eq F A
    }⟩

theorem Morita_iff_Brauer (A B : CSA F): IsMoritaEquivalent A B ↔ IsBrauerEquivalent A B :=
  ⟨fun ⟨⟨e⟩⟩ ↦ by sorry,
  fun ⟨hAB⟩ ↦ by
    obtain ⟨n, m, e⟩ := hAB
    -- obtain ⟨n1⟩ := WedderburnArtin
    sorry⟩

end Field
