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

namespace FftDomain

lemma eq_iff_domains_eq {φ₁ φ₂ : FftDomain ι F} 
  :
  φ₁ = φ₂ ↔ φ₁.domain = φ₂.domain := by
  rcases φ₁ with ⟨f₁, h₁⟩ 
  aesop

end FftDomain

instance : FunLike (FftDomain ι F) ι F where
  coe fftDomain i := fftDomain.domain i
  coe_injective' φ₁ φ₂ h := by
    have h := congrFun h
    aesop (add simp [FftDomain.eq_iff_domains_eq])

namespace FftDomain 

lemma eval_fft_domain_eq_eval_domain
  {fftDomain : FftDomain ι F} {i : ι}
  :
  fftDomain i = fftDomain.domain i := rfl

end FftDomain

instance : Coe (FftDomain ι F) (ι ↪ F) where
  coe fftDomain := ⟨fftDomain, fun i₁ i₂ h => 
    match fftDomain with
    | ⟨domain, hinj⟩ => by aesop (add simp [FftDomain.eval_fft_domain_eq_eval_domain])
  ⟩

set_option synthInstance.checkSynthOrder false in
instance : Membership F (FftDomain ι F) where
  mem φ x := ∃ i, φ i = x

namespace FftDomain 

def toFinset (ω : FftDomain ι F) : Finset F 
  := Finset.image ω Finset.univ 

@[simp]
lemma mem_domain_iff_exists {ω : FftDomain ι F} {x : F}
  :
  x ∈ ω ↔ ∃ i, ω i = x := by rfl

@[simp]
lemma mem_finset_iff_exists {ω : FftDomain ι F} {x : F}
  :
  x ∈ ω.toFinset ↔ ∃ i, ω i = x := by simp [toFinset]

lemma mem_finset_iff_mem_domain {ω : FftDomain ι F} {x : F}
  :
  x ∈ ω.toFinset ↔ x ∈ ω := by simp [toFinset]

end FftDomain
  
instance {x : F} {ω : FftDomain ι F} : Decidable (x ∈ ω) := 
  decidable_of_iff _ FftDomain.mem_finset_iff_mem_domain

namespace Finset

noncomputable def toListWithProof.{u} {α : Type u} [DecidableEq α] (s : Finset α)
  :
  List s := 
  let list := s.toList
  List.reduceOption <|
    list.map (fun x => if h : x ∈ s then some ⟨x, h⟩ else none)

@[simp]
lemma toListWithProof_empty.{u} {α : Type u} [DecidableEq α]
  :
  toListWithProof (∅ : Finset α) = [] := by 
  simp [toListWithProof, List.reduceOption]

lemma toListWithProof_mem.{u} {α : Type u} [DecidableEq α]
  {x : α}
  {s : Finset α}
  (hx : x ∈ s)
  :
  ⟨x, hx⟩ ∈ toListWithProof s := by
  simp [toListWithProof, List.reduceOption, hx]

lemma toListWithProof_eq_toList.{u} {α : Type u} [DecidableEq α]
  {s : Finset α}
  :
  (toListWithProof s).map (fun x => x.1) =
    s.toList := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ih => 
    sorry




end Finset

namespace FftDomain



noncomputable def toList (ω : FftDomain ι F) : List (ω.toFinset) := 
  let list := ω.toFinset.toList
  List.reduceOption <|
    list.map (fun x => if h : x ∈ ω then some ⟨x, by { aesop }⟩ else none)

lemma toList_eq_finset_toList {ω : FftDomain ι F}
  :
  ω.toList.map (fun x => x.1) = ω.toFinset.toList := by  
  rw [ FftDomain.toList, ← List.map_id ( ω.toFinset.toList ) ];
  -- Since every element in the list is in the set, the if condition is always true.
  have h_if_true : ∀ x ∈ ω.toFinset.toList, x ∈ ω.toFinset := by
    aesop;
  -- Since the list is finite, we can apply the definition of `List.reduceOption` directly.
  have h_foldr : ∀ (l : List F), (∀ x ∈ l, x ∈ ω.toFinset) → List.reduceOption (List.map (fun x => if x ∈ ω.toFinset then some x else none) l) = l := by
    intros l hl;
    induction l <;> simp_all +decide [ List.reduceOption ];
  convert h_foldr _ h_if_true;
  · induction' ω.toFinset.toList with x l ih <;> simp +decide [ * ];
    · rfl;
    · split_ifs <;> simp_all +decide [ List.reduceOption ];
  · norm_num


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
lemma mem_subgroup_iff_mem_finset {ω : FftDomain ι F} {x : Fˣ}
  :
  x ∈ ω.toSubgroup ↔ x.val ∈ ω.toFinset := by
  unfold toSubgroup toFinset
  aesop

end FftDomain

instance : CoeOut (FftDomain ι F) (Finset F) where
  coe ω := ω.toFinset

instance : CoeOut (FftDomain ι F) (Subgroup Fˣ) where
  coe ω := ω.toSubgroup

namespace FftDomain


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

namespace FftDomain

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
  

end FftDomain

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

instance : Membership F (CosetFftDomain ι F) where
  mem φ x := ∃ i, φ i = x

namespace CosetFftDomain

def toFinset (ω : CosetFftDomain ι F) : Finset F := 
  Finset.image ω Finset.univ

@[simp]
lemma mem_coset {ω : CosetFftDomain ι F}
  {x : F}
  :
  x ∈ ω.toFinset ↔ ∃ y ∈ ω.fftDomain, x = ω.x * y := by
  simp only [toFinset, Finset.mem_image, Finset.mem_univ, true_and]
  aesop

@[simp]
lemma mem_coset_domain {ω : CosetFftDomain ι F}
  {x : F}
  :
  x ∈ ω ↔ ∃ y ∈ ω.fftDomain, x = ω.x * y := by 
  simp only [Membership.mem, eval_coset_fft_domain_eq_eval_x_mul_domain]
  aesop

lemma mem_coset_finset_iff_mem_coset_domain {ω : CosetFftDomain ι F}
  {x : F}
  :
  x ∈ ω.toFinset ↔ x ∈ ω := by simp
  
end CosetFftDomain

instance {x : F} {ω : CosetFftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ CosetFftDomain.mem_coset_finset_iff_mem_coset_domain

namespace CosetFftDomain

noncomputable def toList (ω : CosetFftDomain ι F) : List (ω.toFinset) := 
  let list := ω.toFinset.toList
  List.reduceOption <|
    list.map (fun x => if h : x ∈ ω then some ⟨x, by aesop⟩ else none)

lemma toList_eq_finset_toList {ω : CosetFftDomain ι F}
  :
  ω.toList.map (fun x => x.1) = ω.toFinset.toList := by  
  rw [ CosetFftDomain.toList, ← List.map_id ( ω.toFinset.toList ) ];
  -- Since every element in the list is in the set, the if condition is always true.
  have h_if_true : ∀ x ∈ ω.toFinset.toList, x ∈ ω.toFinset := by
    aesop;
  -- Since the list is finite, we can apply the definition of `List.reduceOption` directly.
  have h_foldr : ∀ (l : List F), (∀ x ∈ l, x ∈ ω.toFinset) → List.reduceOption (List.map (fun x => if x ∈ ω.toFinset then some x else none) l) = l := by
    intros l hl;
    induction l <;> simp_all +decide [ List.reduceOption ];
  convert h_foldr _ h_if_true;
  · induction' ω.toFinset.toList with x l ih <;> simp +decide [ * ];
    · rfl;
    · split_ifs <;> simp_all +decide [ List.reduceOption ];
  · norm_num

lemma card_eq_fft_domain_card {ω : CosetFftDomain ι F} :
  Finset.card ω.toFinset = Finset.card ω.fftDomain.toFinset := by
  have h_inj : Function.Injective (fun w : F => ω.x * w) := by
    exact mul_right_injective₀ ( Units.ne_zero _ );
  rw [ show ω.toFinset = Finset.image ( fun w : F => ω.x * w ) ω.fftDomain.toFinset from ?_, Finset.card_image_of_injective _ h_inj ];
  simp +decide [ Finset.ext_iff, CosetFftDomain.toFinset, FftDomain.toFinset ];
  aesop 

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

lemma x_mul_mem_coset_iff {φ : CosetFftDomain ι F}
  {y : F}
  :
  φ.x * y ∈ φ ↔ y ∈ φ.fftDomain := by simp

end CosetFftDomain

abbrev SmoothCosetFftDomain (n : ℕ) (F : Type) [Field F] : Type
  := CosetFftDomain (Fin (2 ^ n)) F

namespace FftDomain 

private def subdomain_embed {n : ℕ} (i : Fin n.succ) (k : Fin (2 ^ (i : ℕ)))
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

def subdomain {n : ℕ} (ω : SmoothFftDomain n F) (i : Fin n.succ)
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
  rw [FftDomain.mem_subgroup_iff_mem_finset]
  aesop

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

@[simp]
lemma subdomain_last' {n : ℕ} {ω : SmoothFftDomain n F}
  {v : F}
  :
  v ∈ (ω.subdomain (@Nat.cast (Fin (n + 1)) (Fin.NatCast.instNatCast (n + 1)) n)) ↔ v ∈ ω := by
  simp +decide [ subdomain, toFinset ];
  constructor;
  · aesop;
  · rintro ⟨ a, rfl ⟩;
    use Fin.cast (by simp [Fin.last]) a;
    unfold subdomain_embed; aesop;

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

lemma subdomain_le_finset {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hij : i ≤ j)
  :
  (ω.subdomain i : Finset _) ≤ (ω.subdomain j : Finset F) := by
  unfold FftDomain.toFinset;
  intro x hx;
  have h_subgroup_le : (ω.subdomain i : Subgroup Fˣ) ≤ (ω.subdomain j : Subgroup Fˣ) := by
    exact subdomain_le hij;
  simp_all +decide [ SetLike.le_def ];
  rcases hx with ⟨ a, rfl ⟩ ; specialize h_subgroup_le a rfl; aesop;

lemma subdomain_le_mem {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hij : i ≤ j)
  {x : F}
  (hx : x ∈ ω.subdomain i)
  :
  x ∈ ω.subdomain j := by
  rw [←mem_finset_iff_mem_domain] at hx
  have hx := subdomain_le_finset hij hx
  aesop

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
  simp 
    [Multiplicative.ofAdd, Multiplicative.toAdd, 
     subdomain, FftDomain.eval_fft_domain_eq_eval_domain, subdomain_embed]
  

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
  (h : x ∈ (ω.subdomain i))
  :
  x ^ (2 ^ j.val) ∈ (ω.subdomain (i - j)) := by
  aesop (add simp subdomain_pow_property)

lemma subdomain_roots_card {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {x : F}
  (h : x ∈ (ω.subdomain (i - j)))
  :
  Finset.card {y ∈ (ω.subdomain i) | y ^ (2 ^ j.val) = x}
    = 2 ^ j.val
  := by 
  have h_bijection : Finset.card (Finset.filter (fun y => y.val % 2 ^ (i.val - j.val) = (Classical.choose (FftDomain.mem_domain_iff_exists.mp h)).val) (Finset.univ : Finset (Fin (2 ^ i.val)))) = 2 ^ j.val := by
    rw [ Finset.card_eq_of_bijective ];
    use fun k hk => ⟨ ( Classical.choose ( FftDomain.mem_domain_iff_exists.mp h ) ).val + k * 2 ^ ( i.val - j.val ), by
      have h_card : (Classical.choose (FftDomain.mem_domain_iff_exists.mp h)).val < 2 ^ (i.val - j.val) := by
        convert Fin.is_lt _ using 1;
        simp +decide [ Fin.val_sub, hji ];
        rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ Nat.sub_add_comm ( show ( j : ℕ ) ≤ i from hji ) ];
        · rw [ Nat.mod_eq_of_lt ] <;> omega;
        · omega;
      rw [ show ( 2 : ℕ ) ^ ( i : ℕ ) = 2 ^ ( i.val - j.val ) * 2 ^ ( j.val ) by rw [ ← pow_add, Nat.sub_add_cancel ( show ( j : ℕ ) ≤ i from hji ) ] ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( i.val - j.val ), pow_pos ( zero_lt_two' ℕ ) ( j.val ) ] ⟩;
    · intro a ha
      obtain ⟨k, hk⟩ : ∃ k : ℕ, a.val = (Classical.choose (FftDomain.mem_domain_iff_exists.mp h)).val + k * 2 ^ (i.val - j.val) ∧ k < 2 ^ j.val := by
        norm_num +zetaDelta at *;
        refine' ⟨ a / 2 ^ ( i - j : ℕ ), _, _ ⟩;
        · rw [ ← ha, Nat.mod_add_div' ];
        · exact Nat.div_lt_of_lt_mul <| by rw [ ← pow_add, Nat.sub_add_cancel ( show ( j : ℕ ) ≤ i from hji ) ] ; exact a.2;
      exact ⟨ k, hk.2, Fin.ext hk.1.symm ⟩;
    · simp +decide [ Nat.add_mod, Nat.mod_eq_of_lt ];
      intro k hk; rw [ Nat.mod_eq_of_lt ] ; exact (by
      convert Classical.choose_spec ( FftDomain.mem_domain_iff_exists.mp h ) |> fun h => Fin.is_lt _;
      rw [ Fin.val_sub ];
      rw [ Nat.mod_eq_sub_mod ] <;> norm_num [ Nat.sub_add_comm ( show ( j : ℕ ) ≤ i from hji ) ];
      · rw [ Nat.mod_eq_of_lt ] <;> omega;
      · omega);
    · aesop;
  have h_image : Finset.image (fun k : Fin (2 ^ i.val) => ω.subdomain i k) (Finset.filter (fun y : Fin (2 ^ i.val) => y.val % 2 ^ (i.val - j.val) = (Classical.choose (FftDomain.mem_domain_iff_exists.mp h)).val) (Finset.univ : Finset (Fin (2 ^ i.val)))) = Finset.filter (fun y => y ^ (2 ^ j.val) = x) (ω.subdomain i).toFinset := by
    ext y
    simp [h_bijection];
    constructor <;> intro hy;
    · obtain ⟨ a, ha₁, ha₂ ⟩ := hy; use ⟨ a, ha₂ ⟩ ; have := Classical.choose_spec ( FftDomain.mem_domain_iff_exists.mp h ) ; simp_all +decide [ subdomain_pow_property ] ;
      rw [ ← ha₂, ← this, subdomain_pow_property hji ];
      exact congr_arg _ ( Fin.ext ha₁ );
    · obtain ⟨ ⟨ k, rfl ⟩, hk ⟩ := hy;
      have := Classical.choose_spec ( FftDomain.mem_domain_iff_exists.mp h ) ; simp_all +decide [ subdomain_pow_property ] ;
      have := ω.subdomain ( i - j ) |>.injective ( this.trans hk.symm ) ; aesop;
  rw [ ← h_image, Finset.card_image_of_injective _ ( FftDomain.injective ), h_bijection ]

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

def subdomainNat {n} (ω : SmoothFftDomain n F) (i : ℕ)
  :
  SmoothFftDomain (Fin.ofNat n.succ i) F := 
  ω.subdomain (Fin.ofNat n.succ i)

def subdomainNatReversed {n : ℕ} (ω : SmoothFftDomain n F) (i : ℕ)
  :
  SmoothFftDomain (Fin.ofNat n.succ (n - i)) F := 
  ω.subdomainNat (n - i)


end FftDomain

namespace CosetFftDomain 

section

open FftDomain

def subdomain {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : Fin n.succ)
  :
  SmoothCosetFftDomain i F := 
  ⟨ω.x ^ 2 ^ (n - i.val), ω.fftDomain.subdomain i⟩

@[simp]
lemma subdomain_fftDomain {n} {ω : SmoothCosetFftDomain n F} 
  {i : Fin n.succ}
  :
  (ω.subdomain i).fftDomain = ω.fftDomain.subdomain i := by rfl

lemma subdomain_0 {n : ℕ} {ω : SmoothCosetFftDomain n F}
  :
  (ω.subdomain 0).toFinset = {ω.x.val ^ 2 ^ n} := by
  simp [subdomain, toFinset]

lemma subdomain_n {n : ℕ} {ω : SmoothCosetFftDomain n F}
  :
  (ω.subdomain (Fin.last n)) = ω := by
  aesop 
    (add simp [subdomain
    , FftDomain.subdomain
    , subdomain_embed
    , eval_coset_fft_domain_eq_eval_x_mul_domain])

lemma subdomain_n' {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {v : F}
  :
  v ∈ (ω.subdomain (@Nat.cast (Fin (n + 1)) (Fin.NatCast.instNatCast (n + 1)) n)) ↔ v ∈ ω 
  := Iff.intro
  (by aesop (add simp subdomain))
  (by {
    intro hv
    simp only [mem_coset_domain, mem_domain_iff_exists, exists_exists_eq_and] at hv
    rcases hv with ⟨a, hv⟩ 
    aesop 
      (add simp subdomain)
      (add unsafe [(by (rw [←FftDomain.mem_domain_iff_exists, FftDomain.subdomain_last']))])
  })

lemma subdomain_pow_property {n} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {k : Fin (2 ^ i.val)}
  :
  (ω.subdomain i k) ^ (2 ^ j.val) 
    = (ω.subdomain (i - j) (⟨k.val % 2 ^ (i.val - j.val),
        by {
          convert Nat.mod_lt _ ( pow_pos ( by decide : 0 < 2 ) _ ) using 1;
          aesop 
            (add simp [Fin.val_sub])
            (add unsafe 
              [(by rw [Nat.mod_eq_of_lt]), 
               (by rw [ Nat.mod_eq_sub_mod ])]) 
            (add safe (by omega))
        }
        ⟩)) := by
  simp only [Nat.succ_eq_add_one, subdomain]
  rw [eval_coset_fft_domain_eq_eval_x_mul_domain,
      eval_coset_fft_domain_eq_eval_x_mul_domain,
      Units.val_pow_eq_pow_val,
      mul_pow,
      FftDomain.subdomain_pow_property hji, 
      ←pow_mul, 
      ←pow_add]
  congr
  have key : n.succ - j.val + i.val = (i.val - j.val) + n.succ := by omega
  aesop 
    (add simp [Fin.val_sub])
    (add safe (by omega))
    (add unsafe 
      [(by rw [Nat.mod_eq_of_lt]),]) 

lemma subdomain_pow_property' {n} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {x : F}
  (h : x ∈ (ω.subdomain i))
  :
  x ^ (2 ^ j.val) ∈ (ω.subdomain (i - j)) := by
  rcases h with ⟨u, hu⟩
  aesop (add simp [subdomain_pow_property])


private lemma card_filter_mod_eq' (m b : ℕ) (hbm : b ≤ m) (r : ℕ) (hr : r < 2 ^ b) :
  (Finset.filter (fun k : Fin (2 ^ m) => k.val % 2 ^ b = r) Finset.univ).card = 2 ^ (m - b) := by
  rw [ Finset.card_eq_of_bijective ]
  use fun i hi => ⟨ r + i * 2 ^ b, ?_ ⟩
  all_goals norm_num [ Fin.ext_iff, Nat.add_mod, Nat.mul_mod ]
  · rw [ show 2 ^ m = 2 ^ ( m - b ) * 2 ^ b by rw [ ← pow_add, Nat.sub_add_cancel hbm ] ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) b ]
  · intro a ha; use a / 2 ^ b; rw [ ← ha ] ;
    exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ ← pow_add, Nat.add_sub_of_le hbm ] ; exact a.2, by rw [ Nat.mod_add_div' ] ⟩
  · exact fun i hi => Nat.mod_eq_of_lt hr

lemma subdomain_roots_card {n} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {x : F}
  (h : x ∈ (ω.subdomain (i - j)))
  :
  Finset.card {y | y ∈ (ω.subdomain i) ∧ y ^ (2 ^ j.val) = x}
    = 2 ^ j.val
  := by 
  have h_card : Finset.card {y | y ∈ (ω.subdomain i) ∧ y ^ (2 ^ j.val) = x} =
    Finset.card (Finset.filter (fun k : Fin (2 ^ i.val) => (ω.subdomain i k) ^ (2 ^ j.val) = x) Finset.univ) := by
    rw [show ({y | y ∈ (ω.subdomain i) ∧ y ^ (2 ^ j.val) = x} : Finset F) =
      Finset.image (ω.subdomain i)
        (Finset.filter (fun k : Fin (2 ^ i.val) => (ω.subdomain i k) ^ (2 ^ j.val) = x) Finset.univ) from by
      apply Finset.ext; intro y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨⟨k, rfl⟩, hpow⟩; exact ⟨k, hpow, rfl⟩
      · rintro ⟨k, hpow, rfl⟩; exact ⟨⟨k, rfl⟩, hpow⟩]
    exact Finset.card_image_of_injective _ CosetFftDomain.injective
  rw [h_card]
  -- Step 2: Obtain unique preimage of x
  obtain ⟨r, hr⟩ := h
  -- Step 3: Rewrite the filter condition using subdomain_pow_property + injectivity
  have h_filter_eq : Finset.filter (fun k : Fin (2 ^ i.val) =>
      (ω.subdomain i k) ^ (2 ^ j.val) = x) Finset.univ =
    Finset.filter (fun k : Fin (2 ^ i.val) =>
      k.val % 2 ^ (i.val - j.val) = r.val) Finset.univ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [CosetFftDomain.subdomain_pow_property hji, ← hr]
    exact ⟨fun h => Fin.ext_iff.mp (CosetFftDomain.injective h),
           fun h => congrArg _ (Fin.ext h)⟩
  rw [h_filter_eq]
  -- Step 4: Count using card_filter_mod_eq'
  have hiv : (i - j).val = i.val - j.val := Fin.sub_val_of_le hji
  have hr_lt : r.val < 2 ^ (i.val - j.val) := by
    have := r.isLt; rw [← hiv]; exact this
  rw [card_filter_mod_eq' i.val (i.val - j.val) (by omega) r.val hr_lt]
  congr 1; omega

private lemma fft_neg_one_in_subgroup {n} {ω : SmoothFftDomain n F}
  {i : Fin n.succ} (hi : 0 < i)
  : ∃ k : Fin (2 ^ i.val), (ω.subdomain i k : F) = -1 := by
  -- Let's denote this element as `k = 2^(i-1) : Fin (2^i)`.
  set k : Fin (2 ^ i.val) := ⟨2 ^ (i.val - 1), by
    exact pow_lt_pow_right₀ ( by decide ) ( Nat.pred_lt ( ne_bot_of_gt hi ) )⟩
  generalize_proofs at *;
  -- Since $k$ has additive order 2 in $\text{Fin}(2^i)$, we have $(ω.subdomain i k)^2 = ω.subdomain i (k + k) = ω.subdomain i 0 = 1$.
  have h_order : (ω.subdomain i k) ^ 2 = 1 := by
    have hk_order : (ω.subdomain i k) ^ 2 = (ω.subdomain i (k + k)) := by
      rw [ sq, FftDomain.subdomain ] ; aesop;
    convert hk_order using 1;
    rw [ show k + k = 0 from _ ] ; aesop;
    rcases i with ⟨ _ | i, hi ⟩ <;> norm_num [ Fin.ext_iff, Fin.val_add, Fin.val_mul ] at * ; ring_nf at * ; aesop;
  generalize_proofs at *; (
  -- Since $k$ has additive order 2 in $\text{Fin}(2^i)$, we have $(ω.subdomain i k) \neq 1$.
  have h_ne_one : (ω.subdomain i k) ≠ 1 := by
    have h_ne_one : (ω.subdomain i k) ≠ ω.subdomain i 0 := by
      exact fun h => absurd ( ω.subdomain i |>.injective h ) ( ne_of_gt <| Nat.lt_of_le_of_lt ( Nat.zero_le _ ) <| pow_pos ( by decide ) _ )
    generalize_proofs at *; (
    exact fun h => h_ne_one <| h.trans <| by simp +decide [ FftDomain.subdomain ] ;)
  generalize_proofs at *; (
  exact ⟨ k, Or.resolve_left ( sq_eq_one_iff.mp h_order ) h_ne_one ⟩))

lemma neg_mem_dom_of_mem_dom {n} {ω : SmoothCosetFftDomain n F}
  {i : Fin n.succ}
  {x : F}
  (hi : 0 < i)
  (h : x ∈ (ω.subdomain i))
  :
  -x ∈ (ω.subdomain i) := by
  simp only [mem_coset_domain, FftDomain.mem_domain_iff_exists] at h ⊢
  obtain ⟨y, ⟨k, rfl⟩, rfl⟩ := h
  -- Get the element mapping to -1 in ω.fftDomain.subdomain i
  obtain ⟨k₀, hk₀⟩ := fft_neg_one_in_subgroup (F := F) (ω := ω.fftDomain) (i := i) hi
  -- -x = coset_shift * (fft(-1) * fft(k)) = coset_shift * fft(k₀ + k)
  refine ⟨(ω.subdomain i).fftDomain (k₀ + k), ⟨k₀ + k, rfl⟩, ?_⟩
  simp only [subdomain_fftDomain, FftDomain.domain_add_eq_mul_domain]
  rw [hk₀]
  ring
  
lemma mul_property {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {a b : F}
  (ha : a ∈ (ω.subdomain i))
  (hb : b ∈ (ω.fftDomain.subdomain j))
  :
  a * b ∈ (ω.subdomain i) := by
    rw [ CosetFftDomain.mem_coset_domain ] at *;
    obtain ⟨ y, hy, rfl ⟩ := ha;
    refine' ⟨ y * b, _, _ ⟩;
    · have h_mul : ∀ (a b : F), a ∈ (ω.fftDomain.subdomain i) → b ∈ (ω.fftDomain.subdomain i) → a * b ∈ (ω.fftDomain.subdomain i) := by
        simp +decide [ FftDomain.mem_finset_iff_exists ];
        rintro a b x rfl y rfl; use x + y; simp +decide [ FftDomain.domain_add_eq_mul_domain ] ;
      exact h_mul _ _ hy ( by simpa using FftDomain.subdomain_le_mem hji hb );
    · ring

def subdomainNat {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : ℕ)
  :
  SmoothCosetFftDomain (Fin.ofNat n.succ i) F := 
  ω.subdomain (Fin.ofNat n.succ i)

def subdomainNatReversed {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : ℕ)
  :
  SmoothCosetFftDomain (Fin.ofNat n.succ (n - i)) F := 
  ω.subdomainNat (n - i)

lemma subdomainNatReversed_pow_property' {n} {ω : SmoothCosetFftDomain n F}
  {i j : ℕ} (hsum : j + i ≤ n) {x : F}
  (h : x ∈ (ω.subdomainNatReversed j))
  :
  x ^ (2 ^ i) ∈ (ω.subdomainNatReversed (j + i)) := by
  unfold subdomainNatReversed subdomainNat at *
  set i_fin : Fin n.succ := Fin.ofNat n.succ (n - j) with hi_fin_def
  set j_fin : Fin n.succ := ⟨i, by omega⟩ with hj_fin_def
  have hji : j_fin ≤ i_fin := by
    simp only [j_fin, i_fin, Fin.le_def, Fin.ofNat, Fin.val_mk]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h_eq : i_fin - j_fin = Fin.ofNat n.succ (n - (j + i)) := by
    ext
    simp only [i_fin, j_fin, Fin.val_sub, Fin.ofNat, Fin.val_mk]
    conv_lhs => rw [show (n - j) % n.succ = n - j from Nat.mod_eq_of_lt (by omega)]
    conv_lhs => rw [show n.succ - i + (n - j) = (n - (j + i)) + n.succ * 1 from by omega]
    rw [Nat.add_mul_mod_self_left]
  have key := CosetFftDomain.subdomain_pow_property' hji h
  rw [h_eq] at key
  exact key

lemma subdomainNatReversed_pow_property_main_domain {n} {ω : SmoothCosetFftDomain n F}
  {i : ℕ} {x : F}
  (hi : i ≤ n)
  (h : x ∈ (ω.subdomainNatReversed 0))
  :
  x ^ (2 ^ i) ∈ (ω.subdomainNatReversed i) := by
  unfold subdomainNatReversed subdomainNat at h ⊢
  have hJ : (⟨i, by omega⟩ : Fin (n + 1)) ≤ Fin.ofNat (n + 1) (n - 0) := by
    simp [Fin.le_def, Fin.ofNat]
    omega
  have hsub : Fin.ofNat (n + 1) (n - 0) - ⟨i, by omega⟩ = Fin.ofNat (n + 1) (n - i) := by
    ext
    simp only [Fin.ofNat, Fin.sub_def, Fin.val_mk]
    rw [Nat.mod_eq_of_lt (show n - 0 < n + 1 by omega)]
    have h1 : n + 1 - i + (n - 0) = (n - 0 - i) + 1 * (n + 1) := by omega
    rw [h1, Nat.add_mul_mod_self_right]
    rw [Nat.mod_eq_of_lt (show n - 0 - i < n + 1 by omega)]
    rw [Nat.mod_eq_of_lt (show n - i < n + 1 by omega)]
    omega
  have hval : (⟨i, by omega⟩ : Fin (n + 1)).val = i := rfl
  have key := subdomain_pow_property' hJ h
  rw [hval] at key
  exact hsub ▸ key

lemma subdomainNatReversed_pow_property_main_domain_toFinset {n} {ω : SmoothCosetFftDomain n F}
  {i : ℕ} {x : F}
  (hi : i ≤ n)
  (h : x ∈ (ω.subdomainNatReversed 0).toFinset)
  :
  x ^ (2 ^ i) ∈ (ω.subdomainNatReversed i).toFinset := by
  rw [mem_coset_finset_iff_mem_coset_domain] at *
  exact subdomainNatReversed_pow_property_main_domain hi h

lemma subdomainNat_mul_property {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i j : ℕ} (hji : j ≤ i) (hn : i ≤ n)
  {a b : F}
  (ha : a ∈ (ω.subdomainNat i))
  (hb : b ∈ (ω.fftDomain.subdomainNat j))
  :
  a * b ∈ (ω.subdomainNat i) := by 
  simp only [subdomainNat, FftDomain.subdomainNat] at *
  apply mul_property 
    (j := (Fin.ofNat n.succ j))
    (by {
      simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast]
      rw [Fin.natCast_le_natCast] <;> omega
    }) <;> try tauto

lemma subdomainNatReversed_mul_property {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i j : ℕ} (hji : j ≤ i) (hn : i ≤ n)
  {a b : F}
  (ha : a ∈ (ω.subdomainNatReversed j))
  (hb : b ∈ (ω.fftDomain.subdomainNatReversed i))
  :
  a * b ∈ (ω.subdomainNatReversed j) := by 
  simp only [subdomainNatReversed, FftDomain.subdomainNatReversed] at *
  exact subdomainNat_mul_property (j := n - i) (by omega) (by omega) ha hb

end

end CosetFftDomain

end ReedSolomon
