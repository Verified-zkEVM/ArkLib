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

example (p q : PMF Bool) (f : Bool → Bool) (hmap : p.map f = q) :
    p.map (fun b => f b = true) = q.map (fun b => b = true) :=
  PMF.map_comp_eq_of_map_eq p q f (fun b => b = true) hmap

example :
    (PMF.pure false : PMF Bool).map (fun b => b = true) True ≠
      (PMF.pure true : PMF Bool).map (fun b => b = true) True := by
  norm_num

example :
    (PMF.uniformOfFintype (Fin 2)).map
        (fun n => Equiv.swap (0 : Fin 2) 1 n = 0) True =
      (PMF.uniformOfFintype (Fin 2)).map (fun n => n = 0) True := by
  exact PMF.uniformOfFintype_event_equiv (Equiv.swap 0 1) (fun n : Fin 2 => n = 0)
