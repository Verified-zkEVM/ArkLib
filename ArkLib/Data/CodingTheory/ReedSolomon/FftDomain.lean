import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith

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

def toFinset (ω : FftDomain ι F) : Finset F 
  := Finset.image ω Finset.univ 

def toSubgroup (ω : FftDomain ι F) : Subgroup Fˣ 
  := ⟨⟨⟨Finset.image ω.domain Finset.univ, by {
    intro a b 
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Multiplicative.exists, forall_exists_index]
    intro x ha y hb 
    exists (x + y)
    simp [ha, hb]
  }⟩, by {
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Multiplicative.exists]
    exists 0
    simp
  }⟩, by {
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Multiplicative.exists, forall_exists_index, forall_apply_eq_imp_iff]
    intro a
    exists (-a)
    simp
  }⟩

@[simp]
lemma mem_finset_iff_exists {ω : FftDomain ι F} {x : F}
  :
  x ∈ ω.toFinset ↔ ∃ i, ω i = x := by
  unfold toFinset
  aesop

@[simp]
lemma mem_subgroup_iff_mem_finset {ω : FftDomain ι F} {x : Fˣ}
  :
  x ∈ ω.toSubgroup ↔ x.val ∈ ω.toFinset := by
  unfold toSubgroup toFinset
  aesop

end FftDomain

set_option synthInstance.checkSynthOrder false in
instance : Coe (FftDomain ι F) (Finset F) where
  coe ω := ω.toFinset

set_option synthInstance.checkSynthOrder false in
instance : Coe (FftDomain ι F) (Subgroup Fˣ) where
  coe ω := ω.toSubgroup

namespace FftDomain

@[simp]
lemma mem_subgroup_iff {ω : FftDomain ι F} {x : Fˣ}
  :
  x ∈ (↑ω : Subgroup _) ↔ x.val ∈ Finset.image ω Finset.univ := by aesop

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
lemma injective {ω : FftDomain ι F}
  :
  Function.Injective ω := by 
  intro i₁ i₂ h
  rcases ω with ⟨ω, hinj⟩ 
  simp [eval_fft_domain_eq_eval_domain] at h
  exact hinj (by aesop)

lemma domain_elem_invertible {ω : FftDomain ι F} {i : ι}
  :
  IsUnit (ω i) := by 
  rcases ω with ⟨ω, hinj⟩ 
  simp [eval_fft_domain_eq_eval_domain] 

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

abbrev SmoothFftDomain (n : ℕ) (F : Type) [Field F] : Type
  := FftDomain (Fin (2 ^ n)) F

namespace SmoothFftDomain

@[simp]
lemma size_of_smooth_fft_domain_eq_pow_of_2 {n : ℕ} {ω : SmoothFftDomain n F}
  :
  Finset.card (ω : Finset F) = 2 ^ n := by 
  rw [FftDomain.toFinset, Finset.card_image_of_injective _ FftDomain.injective] 
  simp

private lemma domain_nsmul {n : ℕ} {ω : SmoothFftDomain n F} (k : ℕ) (i : Fin (2 ^ n))
  : ω (k • i) = (ω i) ^ k := by
  induction k with
  | zero => simp [FftDomain.domain_zero_eq_one, pow_zero]
  | succ k ih =>
    rw [succ_nsmul, FftDomain.domain_add_eq_mul_domain, ih, pow_succ]

private lemma val_eq_nsmul_one {n : ℕ} (i : Fin (2 ^ n)) : i = i.val • (1 : Fin (2 ^ n)) := by
  simp +decide [ Fin.ext_iff, Fin.val_add, Fin.val_mul ];
  convert Nat.mod_eq_of_lt i.2 using 1;
  · rw [ Nat.mod_eq_of_lt i.2 ];
  · convert Nat.mod_eq_of_lt i.2 using 1;
    erw [ Fin.val_mk ];
    induction i.val <;> simp_all +decide [ nsmulRec ];
    simp_all +decide [ Fin.val_add, nsmulRec ]

lemma domain_eq_pow_of_generator {n : ℕ} {ω : SmoothFftDomain n F} (i : Fin (2 ^ n))
  : ω i = (ω 1) ^ i.val := by
  conv_lhs => rw [val_eq_nsmul_one i]
  rw [domain_nsmul]

theorem eq_iff_generators_eq {n : ℕ} {ω₁ ω₂ : SmoothFftDomain n F}
  : 
  ω₁ = ω₂ ↔ ω₁ 1 = ω₂ 1 := by
  constructor
  · intro h; rw [h]
  · intro h
    ext i
    rw [domain_eq_pow_of_generator i, domain_eq_pow_of_generator i, h]
  

end SmoothFftDomain

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

end CosetFftDomain

abbrev SmoothCosetFftDomain (n : ℕ) (F : Type) [Field F] : Type
  := CosetFftDomain (Fin (2 ^ n)) F

namespace SmoothFftDomain 

private noncomputable def subdomain_embed {n : ℕ} (i : Fin n.succ) (k : Fin (2 ^ (i : ℕ)))
    : Fin (2 ^ n) :=
  ⟨2 ^ (n - i) * k.val, by
    rcases k with ⟨k, hk⟩
    rcases i with ⟨i, hi⟩
    simp at hk ⊢
    by_cases hk_zero : k = 0
    · subst hk_zero; simp
    · calc 2 ^ (n - i) * k < 2 ^ (n - i) * 2 ^ i :=
            Nat.mul_lt_mul_of_pos_left hk (by positivity)
        _ = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel (by omega)]⟩

private lemma subdomain_embed_add {n : ℕ} (i : Fin n.succ) (a b : Fin (2 ^ (i : ℕ)))
    : subdomain_embed i (a + b) = subdomain_embed i a + subdomain_embed i b := by
  unfold subdomain_embed; simp +decide [ Fin.val_add] ; ring_nf;
  norm_num [ Fin.ext_iff, Fin.val_add, Fin.val_mul ];
  rw [ ← add_mul ];
  rw [ ← Nat.mul_mod_mul_right ];
  rw [ ← pow_add, 
    Nat.add_sub_of_le (Nat.le_of_lt_succ i.2)]

private lemma subdomain_embed_zero {n : ℕ} (i : Fin n.succ)
    : subdomain_embed i (0 : Fin (2 ^ (i : ℕ))) = (0 : Fin (2 ^ n)) := by
  unfold subdomain_embed; aesop;

private lemma subdomain_embed_injective {n : ℕ} (i : Fin n.succ)
    : Function.Injective (subdomain_embed (n := n) i) := by
  intro a b h;
  simp_all +decide [ Fin.ext_iff, subdomain_embed ]

noncomputable def subdomain {n : ℕ} (ω : SmoothFftDomain n F) (i : Fin n.succ)
  :
  SmoothFftDomain i F :=
  ⟨{ toFun := fun k => ω.domain (Multiplicative.ofAdd (subdomain_embed i (Multiplicative.toAdd k)))
     map_one' := by
       simp [subdomain_embed_zero]
     map_mul' := by
       intro a b
       simp only [toAdd_mul]
       rw [subdomain_embed_add]
       exact map_mul ω.domain _ _ },
   by
     intro a b h
     have h2 := ω.inj h
     have h3 := Multiplicative.ofAdd.injective h2
     exact Multiplicative.ofAdd.injective (subdomain_embed_injective i h3)⟩

@[simp]
lemma subdomain_0 {n} {ω : SmoothFftDomain n F}
  :
  (ω.subdomain 0 : Subgroup Fˣ) = ⊥ := by
  ext i
  rw [FftDomain.mem_subgroup_iff]
  simp

private lemma subdomain_embed_last {n : ℕ} (k : Fin (2 ^ (Fin.last n : ℕ)))
  : subdomain_embed (Fin.last n) k = Fin.cast (by simp [Fin.last]) k := by
  unfold subdomain_embed; aesop;

@[simp]
lemma subdomain_last {n} {ω : SmoothFftDomain n F}
  :
  (ω.subdomain (Fin.last n) : Subgroup Fˣ) = (ω : Subgroup Fˣ) := by
  ext x;
  simp +decide [ FftDomain.toSubgroup, subdomain ];
  constructor <;> intro h <;> rcases h with ⟨ a, rfl ⟩ <;> use Fin.cast ( by simp +decide [ Fin.last ] ) a <;> simp +decide [ subdomain_embed_last ] ;

private lemma subdomain_embed_of_le {n : ℕ} (i j : Fin n.succ) (h : i ≤ j)
    (k : Fin (2 ^ (i : ℕ)))
    : ∃ (l : Fin (2 ^ (j : ℕ))), subdomain_embed i k = subdomain_embed j l := by
  refine ⟨⟨2 ^ ((j : ℕ) - (i : ℕ)) * k.val, ?_⟩, ?_⟩
  · calc 2 ^ ((j : ℕ) - (i : ℕ)) * k.val < 2 ^ ((j : ℕ) - (i : ℕ)) * 2 ^ (i : ℕ) := by
          apply Nat.mul_lt_mul_of_pos_left k.isLt (by positivity)
        _ = 2 ^ (j : ℕ) := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  · simp only [subdomain_embed, Fin.ext_iff, Fin.val_mk]
    rw [← mul_assoc, ← pow_add]
    have : n - ↑j + (↑j - ↑i) = n - ↑i := Nat.sub_add_sub_cancel (by omega) (by omega)
    rw [this]

lemma subdomain_le {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (h : i ≤ j)
  :
  (ω.subdomain i : Subgroup _) ≤ (ω.subdomain j : Subgroup Fˣ) := by
  simp +decide [ SetLike.le_def, FftDomain.toSubgroup, FftDomain.mem_subgroup_iff_mem_finset ];
  intro a
  obtain ⟨l, hl⟩ := subdomain_embed_of_le i j h a;
  unfold subdomain; aesop;

private lemma subdomain_embed_pow_eq {n : ℕ} (i j : Fin n.succ) (hji : j.val ≤ i.val)
    (k : Fin (2 ^ i.val))
    : (2 ^ j.val) • (subdomain_embed i k) =
      subdomain_embed ⟨i.val - j.val, by omega⟩
        ⟨k.val % 2 ^ (i.val - j.val), Nat.mod_lt _ (by positivity)⟩ := by
          simp +zetaDelta at *;
          unfold subdomain_embed;
          norm_num [ Fin.ext_iff ];
          erw [ Fin.val_mk ];
          -- By definition of nsmulRec, we have:
          have h_nsmulRec : ∀ (p : ℕ) (x : Fin (2 ^ n)), (nsmulRec p x : Fin (2 ^ n)).val = (p * x.val) % 2 ^ n := by
            intro p x; induction' p with p ih generalizing x <;> simp +decide [ *, nsmulRec ] ;
            simp +decide [ add_mul, Fin.val_add, Nat.add_mod, ih ];
          rw [ h_nsmulRec ];
          rw [ ← Nat.mul_mod_mul_left ];
          rw [ ← pow_add, tsub_tsub_assoc ] <;> norm_num [ hji ];
          · rw [ show n - i + i = n by rw [ tsub_add_cancel_of_le ( by linarith [ Fin.is_lt i ] ) ] ] ; ring;
          · exact Fin.is_le i

private lemma subdomain_eval {n : ℕ} {ω : SmoothFftDomain n F} (i : Fin n.succ) (k : Fin (2 ^ i.val))
    : (ω.subdomain i k : F) = ω (subdomain_embed i k) := by
  simp [subdomain, FftDomain.eval_fft_domain_eq_eval_domain, subdomain_embed]
  rfl

private lemma subdomain_pow_property_aux {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {k : Fin (2 ^ i.val)}
  :
  (ω.subdomain i k) ^ (2 ^ j.val) 
    = (ω.subdomain ⟨i.val - j.val, by omega⟩ (⟨k.val % 2 ^ (i.val - j.val), 
        Nat.mod_lt _ (by positivity)⟩)) := by
  rw [subdomain_eval, ← domain_nsmul, subdomain_eval, subdomain_embed_pow_eq i j hji]

lemma subdomain_pow_property {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {k : Fin (2 ^ i.val)}
  :
  (ω.subdomain i k) ^ (2 ^ j.val) 
    = (ω.subdomain (i - j) (⟨k.val % 2 ^ (i.val - j.val),
        by {
          convert Nat.mod_lt _ ( pow_pos ( by decide : 0 < 2 ) _ ) using 1;
          simp +decide [ Fin.val_sub ];
          rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ hji ];
          · rw [ Nat.mod_eq_of_lt ];
            · omega;
            · omega;
          · omega
        }
        ⟩)) := by
  rw [subdomain_pow_property_aux hji] 
  convert rfl;
  · exact Fin.sub_val_of_le hji;
  · exact Fin.sub_val_of_le hji;
  · exact Fin.sub_val_of_le hji;
  · exact Fin.sub_val_of_le hji;
  · exact Fin.sub_val_of_le hji

lemma subdomain_pow_property' {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {x : F}
  (h : x ∈ (ω.subdomain i).toFinset)
  :
  x ^ (2 ^ j.val) ∈ (ω.subdomain (i - j)).toFinset := by
  simp only [Nat.succ_eq_add_one, FftDomain.mem_finset_iff_exists] at h
  rcases h with ⟨u, hu⟩ 
  rw [←hu, subdomain_pow_property hji]
  simp

lemma subdomain_roots_card {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {x : F}
  (h : x ∈ (ω.subdomain (i - j)).toFinset)
  :
  Finset.card {y ∈ (ω.subdomain i).toFinset | y ^ (2 ^ j.val) = x}
    = 2 ^ j.val
  := by 
  sorry

lemma subdomain_subdomain_eq_subdomain {n} {ω : SmoothFftDomain n F}
  {i : Fin n.succ} {j : Fin i.val.succ} 
  :
  (ω.subdomain i).subdomain j = ω.subdomain (Fin.castLE (by omega) j) := by
    ext x
    rw [subdomain_eval]
    rw [subdomain_eval]
    trans (ω (subdomain_embed (Fin.castLE (by omega) j) x))
    · simp only [subdomain_embed] 
      apply congrArg
      simp only [Nat.succ_eq_add_one, Fin.val_castLE, Fin.mk.injEq]
      rw [←mul_assoc]
      rw [←pow_add]
      simp only [mul_eq_mul_right_iff, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
        pow_right_inj₀, Fin.val_eq_zero_iff]
      left
      omega
    · rfl

end SmoothFftDomain

namespace SmoothCosetFftDomain 

def subdomain {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : Fin n)
  :
  SmoothCosetFftDomain (n - i) F := sorry

end SmoothCosetFftDomain

end ReedSolomon
