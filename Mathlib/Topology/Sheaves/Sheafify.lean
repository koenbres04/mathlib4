/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.LocalPredicate

import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheafification of `Type`-valued presheaves

We construct the sheafification of a `Type`-valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.

We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalkToFiber` which evaluates a germ of a dependent function at a point.

We construct a morphism `toSheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.

## Future work
Show that the map induced on stalks by `toSheafify` is the inverse of `stalkToFiber`.

Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor,
following <https://stacks.math.columbia.edu/tag/007X>.
-/

@[expose] public section

assert_not_exists CommRingCat


universe v u

noncomputable section

open TopCat Opposite TopologicalSpace CategoryTheory

variable {X : TopCat.{v}}

namespace TopCat.Presheaf

section Notation

variable {C : Type u} [Category.{v} C] [HasWeakSheafify (Opens.grothendieckTopology X) C]

def sheafify (F : Presheaf C X) : Presheaf C X :=
  (CategoryTheory.sheafify (Opens.grothendieckTopology X) F)

lemma sheafify_isSheaf (F : Presheaf C X) : IsSheaf (sheafify F) :=
  CategoryTheory.Presheaf.sheafify_isSheaf _ F

def toSheafify (F : Presheaf C X) : F ⟶ F.sheafify :=
  (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F)

end Notation

section StalkFunctorIso

variable (p₀ : X) (C : Type u) [Category.{v} C] [Limits.HasColimits C]
  [Limits.HasTerminal C] (𝓕 : Presheaf C X) [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- Given a presheaf `𝓕`, the induced map on stalks of `CategoryTheory.toSheafify`, `𝓕ₓ ⟶ 𝓕⁺ₓ`,
is an isomorphism -/
theorem stalkFunctor_map_unit_toSheafify_isIso :
  IsIso ((stalkFunctor C p₀).map (toSheafify 𝓕)) := by
  classical
  exact Adjunction.isIso_map_unit_of_isLeftAdjoint_comp (sheafificationAdjunction _ C)
    (skyscraperSheafForgetAdjunction p₀)

end StalkFunctorIso


section

variable {C : Type u} [Category.{v} C] [Limits.HasColimits C] [Limits.HasTerminal C]
  [HasWeakSheafify (Opens.grothendieckTopology X) C]
  {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC]


theorem germ_eq_of_sheafify_eq {F : Presheaf C X} {U : Opens X} (x : X) (x_mem : x ∈ U)
  {s t : CC (F.obj (op U))} (h : F.toSheafify.app (op U) s = F.toSheafify.app (op U) t)
  : germ F U x x_mem s = germ F U x x_mem t := by
  have : IsIso ((stalkFunctor C x).map F.toSheafify) := stalkFunctor_map_unit_toSheafify_isIso x C F
  apply (ConcreteCategory.bijective_of_isIso ((stalkFunctor C x).map F.toSheafify)).left
  simp only [stalkFunctor_map_germ_apply]
  congr 1
end


section TempSectionName

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

variable [HasSheafify (Opens.grothendieckTopology X) C] [Limits.HasColimits C] [Limits.HasLimits C]



open scoped AlgebraicGeometry

namespace Sheafify


structure SectionPresentation {F : Presheaf C X} {U : Opens X}
  (t : CC ((sheafify F).obj (op U))) where
  α : Type v
  V : α → Set X
  V_open : ∀ a, IsOpen (V a)
  V_cover : ⋃ a, V a = U.carrier
  s : (a : α) → CC (F.obj (op (⟨V a, V_open a⟩)))
  V_le : ∀ a, V a ≤ U
  t_restrict : ∀ a, t |_ₗ (⟨V a, V_open a⟩) ⟪V_le a⟫ = ((toSheafify F).app _) (s a)


def SectionPresentation.V_opens {F : Presheaf C X} {U : Opens X}
  {t : CC ((sheafify F).obj (op U))} (pres : SectionPresentation t) : pres.α → Opens X :=
  fun a => ⟨pres.V a, pres.V_open a⟩


lemma SectionPresentation.s_germ_eq {F : Presheaf C X} {U : Opens X}
  {t : CC ((sheafify F).obj (op U))} (pres : SectionPresentation t) (a b : pres.α)
  (x : X) (x_mem_Va : x ∈ pres.V a) (x_mem_Vb : x ∈ pres.V b) :
  F.germ (pres.V_opens a) x x_mem_Va (pres.s a) = F.germ (pres.V_opens b) x x_mem_Vb (pres.s b)
  := by
  let Vab := pres.V_opens a ⊓ pres.V_opens b
  have x_mem_Vab : x ∈ Vab := Opens.mem_inf.mpr ⟨x_mem_Va, x_mem_Vb⟩
  have : Vab ≤ U := inf_le_left.trans (pres.V_le a)
  have : pres.V_opens a ≤ U := pres.V_le a
  have : pres.V_opens b ≤ U := pres.V_le b
  have : ((toSheafify F).app (op Vab)) ((pres.s a) |_ Vab)
    = ((toSheafify F).app (op Vab)) ((pres.s b) |_ Vab) := by
      calc
        _ = ((toSheafify F).app (op (pres.V_opens a))) (pres.s a) |_ Vab := by apply map_restrict
        _ = t |_ (pres.V_opens a) |_ Vab := by congr 1; symm; apply pres.t_restrict
        _ = t |_ (pres.V_opens b) |_ Vab := by simp only [restrict_restrict]
        _ = ((toSheafify F).app (op (pres.V_opens b))) (pres.s b) |_ Vab := by
          congr 1; apply pres.t_restrict
        _ = ((toSheafify F).app (op Vab)) ((pres.s b) |_ Vab) := by symm; apply map_restrict
  have : F.germ Vab x x_mem_Vab ((pres.s a) |_ Vab) = F.germ Vab x x_mem_Vab ((pres.s b) |_ Vab)
    := germ_eq_of_sheafify_eq x x_mem_Vab this
  simp only [restrict, germ_res_apply] at this
  assumption


variable [(forget C).ReflectsIsomorphisms]
  [Limits.PreservesFilteredColimits (forget C)] [Limits.PreservesLimits (forget C)]

instance : (Opens.grothendieckTopology X).PreservesSheafification (forget C) := by infer_instance

instance : (Opens.grothendieckTopology X).HasSheafCompose (forget C) := by infer_instance


instance existsSectionPresentation {F : Presheaf C X} {U : Opens X}
  (t : CC ((sheafify F).obj (op U))) : Nonempty (Sheafify.SectionPresentation t) := by
  have : ∀ (V t'), ∀ x ∈ V, ∃ (W : _) (_ : W ≤ V),
         (∃ s, ((toSheafify F).app _) s = t' |_ W) ∧ x ∈ W := by
    rw [← isLocallySurjective_iff, IsLocallySurjective]
    apply Presheaf.isLocallySurjective_toSheafify' (Opens.grothendieckTopology X) F
  choose W W_le hW using this U t
  have x_mem := fun x hx ↦ (hW x hx).2
  choose s hs using fun x hx ↦ (hW x hx).1
  refine ⟨?α, ?V, ?V_open, ?V_cover, ?s, ?V_le, ?t_restrict⟩
  · exact U.carrier.Elem
  · exact fun ⟨x, hx⟩ => W x hx
  · intro a; apply Opens.isOpen
  · ext x
    rw [Set.mem_iUnion]
    simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe, SetLike.mem_coe, Subtype.exists]
    constructor
    · rintro ⟨y, ⟨y_mem, hx⟩⟩
      exact (W_le y _) hx
    · intro hx
      exact ⟨x, ⟨hx, x_mem x hx⟩⟩
  · exact fun ⟨x, hx⟩ => s x hx
  · exact fun ⟨x, hx⟩ => W_le x hx
  · exact fun ⟨x, hx⟩ => (hs x hx).symm


end Sheafify

end TempSectionName

end TopCat.Presheaf
