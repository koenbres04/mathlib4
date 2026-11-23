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

end TopCat.Presheaf
