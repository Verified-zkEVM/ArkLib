import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs

namespace ReedSolomon

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

structure FftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] where 
    domain : MonoidHom (Multiplicative ι) Fˣ 
    inj : Function.Injective domain

instance : FunLike (FftDomain ι F) ι F where
  coe fftDomain i := fftDomain.domain i
  coe_injective' := by
    rintro ⟨f₁, h₁⟩ ⟨f₂, h₂⟩ h 
    simp only at h
    simp only [FftDomain.mk.injEq]
    ext i
    simp only [MonoidHom.toAdditiveRight_apply_apply, Multiplicative.ofAdd, Equiv.coe_fn_mk,
      toMul_ofMul]
    exact (congrFun h i)

namespace FftDomain 

omit [Fintype ι] [Fintype F] [DecidableEq ι] [DecidableEq F] in
lemma eval_fft_domain_eq_eval_domain
  {fftDomain : FftDomain ι F} {i : ι}
  :
  fftDomain i = fftDomain.domain i := rfl

end FftDomain

instance : Coe (FftDomain ι F) (ι ↪ F) where
  coe fftDomain := ⟨fftDomain, by {
    intro i₁ i₂ h
    rcases fftDomain with ⟨domain, hinj⟩
    simp [FftDomain.eval_fft_domain_eq_eval_domain] at h
    simp only [Function.Injective, Multiplicative.forall, EmbeddingLike.apply_eq_iff_eq] at hinj 
    specialize hinj i₁ i₂ 
    simp only [Multiplicative.ofAdd, Equiv.coe_fn_mk] at hinj 
    apply hinj
    aesop
  }⟩

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
lemma injective {ω : FftDomain ι F}
  :
  Function.Injective ω := by 
  intro i₁ i₂ h
  rcases ω with ⟨ω, hinj⟩ 
  simp [eval_fft_domain_eq_eval_domain] at h
  exact hinj (by aesop)

@[simp]
lemma domain_zero_eq_one {ω : FftDomain ι F} 
  :
  ω 0 = 1 := by 
  show ↑(ω.domain (Multiplicative.ofAdd (0 : ι))) = (1 : F)
  rw [show Multiplicative.ofAdd (0 : ι) = (1 : Multiplicative ι) from rfl, map_one]
  simp

@[simp]
lemma domain_add_eq_mul_domain {ω : FftDomain ι F}
  {i₁ i₂ : ι}
  :
  ω (i₁ + i₂) = ω i₁ * ω i₂ := by
  convert congr_arg 
    ( fun x : Fˣ => ( x : F ) ) 
    ( ω.domain.map_mul ( Multiplicative.ofAdd i₁ ) ( Multiplicative.ofAdd i₂ ) ) using 1 
  
@[simp]
lemma domain_neg_eq_inv_domain {ω : FftDomain ι F}
  {i₁ : ι}
  :
  ω (-i₁) = (ω i₁)⁻¹ := by 
  have h_def : ω (-i₁) * ω i₁ = 1 := by
    rw [ ← FftDomain.domain_add_eq_mul_domain ] ; aesop;
  exact eq_inv_of_mul_eq_one_left h_def


@[simp]
lemma domain_sub_eq_div_domain {ω : FftDomain ι F}
  {i₁ i₂ : ι}
  :
  ω (i₁ - i₂) = ω i₁ / ω i₂ := by
  rw 
    [sub_eq_add_neg, 
      div_eq_mul_inv, 
      FftDomain.domain_add_eq_mul_domain, 
      FftDomain.domain_neg_eq_inv_domain ];

def size (_ω : FftDomain ι F) : ℕ := Fintype.card ι 

@[simp]
lemma card_of_image_eq_size {ω : FftDomain ι F}
  :
  (Finset.image ω Finset.univ).card = ω.size := by 
  apply Finset.card_image_of_injective;
  intro i j h_eq
  apply ω.inj
  exact Units.val_injective.eq_iff.mp h_eq

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
@[ext]
theorem ext {ω₁ ω₂ : FftDomain ι F} (h : ∀ i, ω₁ i = ω₂ i)
  :
  ω₁ = ω₂ := by 
  rcases ω₁ with ⟨f₁, _⟩ 
  rcases ω₂ with ⟨f₂, _⟩ 
  simp only [mk.injEq]
  ext i
  simp [Multiplicative.ofAdd]
  specialize (h i)
  aesop

end FftDomain

structure SmoothFftDomain (n : ℕ) (ι : Type) [AddCommGroup ι] 
  [Fintype ι] [SMul ℤ ι]
  (F : Type) [Field F] extends FftDomain ι F where
  smooth_size : Fintype.card ι = 2 ^ n
  is_cyclic : IsAddCyclic ι 

instance {n} : FunLike (SmoothFftDomain n ι F) ι F where
  coe fftDomain i := fftDomain.domain i
  coe_injective' := by
    rintro ⟨⟨f₁, _⟩, _, _, _⟩ ⟨⟨f₂, _⟩, _, _, _⟩ h 
    simp only at h
    simp only [SmoothFftDomain.mk.injEq, FftDomain.mk.injEq]
    ext i
    simp only [MonoidHom.toAdditiveRight_apply_apply, Multiplicative.ofAdd, Equiv.coe_fn_mk,
      toMul_ofMul]
    exact (congrFun h i)

noncomputable def generator {n : ℕ} (ω : SmoothFftDomain n ι F) 
  : 
  F := ω <| 
    Classical.choose (@exists_zsmul_surjective ι _ ω.is_cyclic)

structure CosetFftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] where
  x : Fˣ 
  fftDomain : FftDomain ι F

instance : FunLike (CosetFftDomain ι F) ι F where
  coe cosetDomain i := cosetDomain.x * cosetDomain.fftDomain i
  coe_injective' := by
    rintro ⟨x₁, f₁⟩ ⟨x₂, f₂⟩ h 
    simp only at h
    simp only [CosetFftDomain.mk.injEq]
    have hx : x₁ = x₂ := by
      have h := congrFun h 0
      aesop
    subst hx
    simp only [true_and]
    ext i
    have h := congrFun h i
    simp only [mul_eq_mul_left_iff, Units.ne_zero, or_false] at h
    exact h

namespace CosetFftDomain 

lemma eval_coset_fft_domain_eq_eval_x_mul_domain
  {cosetDomain : CosetFftDomain ι F} {i : ι}
  :
  cosetDomain i = cosetDomain.x * cosetDomain.fftDomain i := rfl

end CosetFftDomain

instance : Coe (CosetFftDomain ι F) (ι ↪ F) where
  coe cosetDomain := ⟨cosetDomain, by {
    intro i₁ i₂ h
    rcases cosetDomain with ⟨x, f⟩
    simp only [CosetFftDomain.eval_coset_fft_domain_eq_eval_x_mul_domain, mul_eq_mul_left_iff,
      Units.ne_zero, or_false] at h
    exact FftDomain.injective h
  }⟩

namespace CosetFftDomain

lemma injective {ω : CosetFftDomain ι F}
  :
  Function.Injective ω := by 
  intro i₁ i₂ h
  rcases ω with ⟨x, ω⟩ 
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain] at h
  exact FftDomain.injective (by aesop)

@[simp]
lemma coset_domain_zero_eq_x {ω : CosetFftDomain ι F} 
  :
  ω 0 = ω.x := by 
  rcases ω with ⟨x, ω⟩
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain]

@[simp]
lemma coset_domain_add_eq_mul_domain {ω : CosetFftDomain ι F}
  {i₁ i₂ : ι}
  :
  ω (i₁ + i₂) = (ω.x)⁻¹ * ω i₁ * ω i₂ := by
  rcases ω with ⟨x, ω⟩
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain]
  ring_nf
  
@[simp]
lemma coset_domain_neg_eq_inv_domain {ω : CosetFftDomain ι F}
  {i₁ : ι}
  :
  ω (-i₁) = ω.x ^ 2 * (ω i₁)⁻¹ := by 
  rcases ω with ⟨x, ω⟩
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain]
  ring_nf
  rw [mul_comm ((↑x : F) ^ 2)]
  have h : (↑x : F) ^ 2 = x * x := by ring_nf
  rw [h]
  rw [mul_assoc, mul_assoc]
  rw [Field.mul_inv_cancel _ (by simp)]
  ring_nf

@[simp]
lemma coset_domain_sub_eq_div_domain {ω : CosetFftDomain ι F}
  {i₁ i₂ : ι}
  :
  ω (i₁ - i₂) = ω.x * ω i₁ / ω i₂ := by
  rcases ω with ⟨x, ω⟩
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain]
  ring_nf
  rw [mul_comm ((↑x : F) ^ 2), mul_assoc (ω i₁), 
    mul_assoc (ω i₁), mul_comm ((↑x : F) ^ 2), mul_assoc (_⁻¹)]
  have h : (↑x : F)^ 2 = x * x := by ring_nf
  rw [h, mul_assoc (↑x : F) (↑x : F), Field.mul_inv_cancel _ (by simp)]
  ring_nf

def size (_ω : CosetFftDomain ι F) : ℕ := Fintype.card ι 

@[simp]
lemma card_of_image_eq_size {ω : CosetFftDomain ι F}
  :
  (Finset.image ω Finset.univ).card = ω.size := 
    Finset.card_image_of_injective _ injective

@[ext]
theorem ext {ω₁ ω₂ : CosetFftDomain ι F} (h : ∀ i, ω₁ i = ω₂ i)
  :
  ω₁ = ω₂ := by 
  rcases ω₁ with ⟨x₁, f₁⟩ 
  rcases ω₂ with ⟨x₂, f₂⟩ 
  have hx : x₁ = x₂ := by 
    specialize (h 0)
    aesop
  simp only [hx, mk.injEq, true_and]
  ext i
  specialize (h i)
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain] at h
  aesop

class CosetSmooth (n : ℕ) (ω : CosetFftDomain ι F) where
  fftSmooth : FftDomain.Smooth n ω.fftDomain

end CosetFftDomain


end ReedSolomon
