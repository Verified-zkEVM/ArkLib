import ArkLib.Data.Probability.PMF

open scoped ENNReal

example {α : Type*} (p : PMF α) (P : α → Prop) [DecidablePred P] :
    (p.map P) True = ∑' a, p a * (if P a then (1 : ENNReal) else 0) :=
  PMF.map_true_eq_tsum_indicator p P

example :
    (PMF.pure true : PMF Bool).map (fun b => b = true) True = 1 := by
  rw [PMF.map_true_eq_tsum_indicator]
  simp

example :
    (PMF.uniformOfFintype (Fin 2)).map (fun n => n = 0) True = (1 / 2 : ENNReal) := by
  rw [PMF.map_true_eq_tsum_indicator]
  norm_num [PMF.uniformOfFintype_apply]

example :
    (PMF.pure true : PMF Bool).map Bool.not = (PMF.pure false : PMF Bool) := by
  simpa using (PMF.pure_map (f := Bool.not) true)

example : ((PMF.pure true : PMF Bool).map Bool.not) false = 1 := by
  rw [PMF.pure_map]
  simp

example :
    ((PMF.pure true : PMF Bool).map (fun b => Bool.not b = false)) True =
      ((PMF.pure false : PMF Bool).map (fun b => b = false)) True := by
  have hmap :
      (PMF.pure true : PMF Bool).map Bool.not = (PMF.pure false : PMF Bool) := by
    simpa using (PMF.pure_map (f := Bool.not) true)
  exact congrArg (fun p : PMF Prop => p True)
    (PMF.map_comp_eq_of_map_eq _ _ Bool.not (fun b => b = false) hmap)

example :
    (PMF.pure false : PMF Bool).map (fun b => b = true) True ≠
      (PMF.pure true : PMF Bool).map (fun b => b = true) True := by
  norm_num

example :
    (PMF.uniformOfFintype (Fin 2)).map
        (fun n => Equiv.swap (0 : Fin 2) 1 n = 0) True =
      (PMF.uniformOfFintype (Fin 2)).map (fun n => n = 0) True := by
  exact PMF.uniformOfFintype_event_equiv (Equiv.swap 0 1) (fun n : Fin 2 => n = 0)

example :
    (PMF.uniformOfFintype (Fin 2)).map (Equiv.swap 0 1) =
      PMF.uniformOfFintype (Fin 2) := by
  exact PMF.uniformOfFintype_map_equiv (Equiv.swap 0 1)

example {F : Type} [Nonempty F] [Fintype F] :
    (do
      let x ← PMF.uniformOfFintype F
      let y ← PMF.uniformOfFintype F
      let z ← PMF.uniformOfFintype (F × F)
      return z = (x, y) : PMF Prop).1 True =
        ((1 : ENNReal) / Fintype.card (F × F)) := by
  classical
  simp [Bind.bind, Pure.pure, PMF.bind]
  simp [DFunLike.coe]
  ring_nf
  rw [mul_comm (_ ^ 2) _, mul_assoc, ENNReal.mul_inv_cancel, mul_one, ENNReal.inv_pow]
  <;> aesop
