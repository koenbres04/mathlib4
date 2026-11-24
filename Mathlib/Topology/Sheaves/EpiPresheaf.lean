/-
Copyright (c) 2026 Koen Bresters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koen Bresters
-/


module

public import Mathlib.Logic.Function.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Sheaves.Sheafify

import Mathlib.Topology.ShrinkingLemma

/-!
# Epipresheaves

We define epipresheaf

## Main definition

* `TopCat.Pressheaf.IsEpiPresheaf`: A presheaf is an epipresheaf if it satisfies gluing, but not
  necessarily uniquely.

## Main results

* `TopCat.Presheaf.IsEpiPresheaf.toSheafify_app_surjective`: On a paracompact Hausdorff space, the
  comparison map between the sections of an epipresheaf and the sections of its sheafification is
  surjective on global sections.
-/

noncomputable section

open TopCat TopCat.Presheaf CategoryTheory Functor
  TopologicalSpace TopologicalSpace.Opens Opposite Limits Function


open scoped AlgebraicGeometry

universe u v x

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]


namespace TopCat

namespace Presheaf

section Definition

variable {X : TopCat.{v}} (F : Presheaf C X)

public def IsEpiPresheaf : Prop :=
  ∀ ⦃ι : Type v⦄ (U : ι → Opens X) (sf : ∀ i : ι, ToType (F.obj (op (U i)))),
        IsCompatible F U sf → ∃ s : ToType (F.obj (op (iSup U))), IsGluing F U sf s

end Definition



section TheProofTemp


namespace IsEpiPresheaf

variable {X : TopCat.{v}} [HasSheafify (Opens.grothendieckTopology X) C]
variable [Limits.HasColimits C] [Limits.HasLimits C]
variable [Limits.PreservesFilteredColimits (forget C)] [ReflectsIsomorphisms (forget C)]
variable [PreservesLimits (forget C)]

variable {F : Presheaf C X} (F_epipresheaf : IsEpiPresheaf F)
variable [ParacompactSpace X] [T2Space X]


-- TODO: have instance search acutally work on NonEmpty (Sheafify.SectionPresentation t)
-- TODO: add docstring with reference to bredon
-- TODO: weaken assumption to having mere gluing just covers of univ
public lemma toSheafify_app_surjective (F_epipresheaf : IsEpiPresheaf F)
  (subsingleton_on_bot : Subsingleton (CC (F.obj (op ⊥)))) :
  Surjective ((toSheafify F).app (op ⊤)) := by
  classical
  intro t
  rcases Sheafify.existsSectionPresentation t with ⟨α, U, U_open, U_cover, sf, U_le, t_restrict⟩
  rcases precise_refinement U U_open U_cover with ⟨V, ⟨V_open, V_cover, V_loc_fin, V_le⟩⟩
  -- apply the shrinking lemma and use it to construct the I-sets
  rcases exists_iUnion_eq_closure_subset V_open V_loc_fin.point_finite V_cover with
    ⟨W, W_cover, W_open, W_closure_le⟩
  let I : X → Set α := fun x => { a | x ∈ closure (W a) }
  have I_fin : ∀ x, Finite (I x) := by
    intro x
    apply (V_loc_fin.point_finite x).subset
    intro a hx
    exact W_closure_le a hx
  -- define open neighbourhoods B x and prove properties
  have : ∀ x, ∃ B ⊆ ⋂ a, ⋂ (_ : x ∉ closure (W a)), (closure (W a))ᶜ, IsOpen B ∧ x ∈ B := by
    intro x
    rw [← mem_nhds_iff]
    exact V_loc_fin.subset W_closure_le |>.iInter_compl_mem_nhds (fun _ => isClosed_closure) x
  choose B B_subset B_open_nhd using this
  -- define open neighbourhoods D x and prove properties
  have sf_germs_eq : ∀ x a (ha : a ∈ I x) b (hb : b ∈ I x),
    F.germ ⟨U a, U_open _⟩ x (ha |> W_closure_le a |> V_le a) (sf a)
    = F.germ ⟨U b, U_open _⟩ x (hb |> W_closure_le b |> V_le b) (sf b) := by
    intro x a ha b hb
    exact (⟨α, U, U_open, U_cover, sf, U_le, t_restrict⟩ : Sheafify.SectionPresentation _).s_germ_eq
      a b x _ _
  have : ∀ x, ∃ (D : _) (D_subset : ∀ a ∈ I x, D ⊆ U a) (D_open : IsOpen D) (D_mem: x ∈ D),
    ∀ a (ha : a ∈ I x) b (hb : b ∈ I x),
    sf a |_ₗ ⟨D, D_open⟩ ⟪D_subset a ha⟫ =
    sf b |_ₗ ⟨D, D_open⟩ ⟪D_subset b hb⟫ := by
    intro x
    choose D D_mem D_le D_prop using germ_eq_finite F
      (fun (a_I : I x) => ⟨U a_I.val, U_open a_I.val⟩) x
      (fun a_I => a_I.prop |> W_closure_le a_I.val |> V_le _)
      (fun a_I => sf a_I.val)
      (fun a_I b_I => sf_germs_eq x a_I.val a_I.prop b_I.val b_I.prop)
    refine ⟨D, ?_, ?_, ?_, ?_⟩
    · intro a ha; exact (D_le ⟨a, ha⟩).down.down
    · exact D.is_open'
    · exact D_mem
    · intro a ha b hb; exact D_prop ⟨a, ha⟩ ⟨b, hb⟩
  choose D D_subset D_open D_mem D_restrict using this
  -- define N as the intersection of B and C and prove properties
  let N : X → Set X := fun x => B x ∩ D x
  have N_open : ∀x, IsOpen (N x) := by
    intro x; exact IsOpen.inter (B_open_nhd x |>.left) (D_open x)
  have N_mem : ∀ x, x ∈ N x := by
    intro x; exact Set.mem_inter (B_open_nhd x |>.right) (D_mem x)
  have N_le_U : ∀x, ∀a ∈ I x, N x ≤ U a := by
    intro x a ha
    exact Set.inter_subset_right.trans (D_subset x a ha)
  have N_I_le : ∀x, ∀y ∈ N x, I y ⊆ I x := by
    intro x y hy a ha
    by_contra hx
    have := by calc
      N x ⊆ B x := Set.inter_subset_left
      _ ⊆ ⋂ a, ⋂ (_ : x ∉ closure (W a)), (closure (W a))ᶜ := B_subset x
      _ ⊆ ⋂ (_ : x ∉ closure (W a)), (closure (W a))ᶜ := Set.iInter_subset _ _
      _ ⊆ (closure (W a))ᶜ := Set.iInter_subset _ hx
    have : y ∈ (closure (W a))ᶜ := this hy
    contradiction
  -- view N as a family of 'Opens' and prove properties about this
  let N_opens : X → Opens X := fun x => ⟨N x, N_open x⟩
  have N_opens_sup : iSup N_opens = ⊤ := by
    rw [← Opens.coe_eq_univ, Opens.coe_iSup, Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_iUnion]
    use x; exact N_mem x
  have N_s_agree : ∀x, ∀a (ha : a ∈ I x), ∀ b (hb : b ∈ I x),
    (sf a) |_ₗ (N_opens x) ⟪N_le_U x a ha⟫ = (sf b) |_ₗ (N_opens x) ⟪N_le_U x b hb⟫ := by
    intro x a ha b hb
    have : N x ⊆ U a:= N_le_U x a ha
    have : N x ⊆ U b := N_le_U x b hb
    have : D x ⊆ U a := D_subset x a ha
    have : D x ⊆ U b := D_subset x b hb
    have : N x ⊆ D x := Set.inter_subset_right
    change (sf a) |_ (N_opens x) = (sf b) |_ (N_opens x)
    calc
      (sf a) |_ (N_opens x) = ((sf a) |_ ⟨D x, D_open x⟩) |_ (N_opens x) := by
        symm; apply restrict_restrict
      _ = ((sf b) |_ ⟨D x, D_open x⟩) |_ (N_opens x) := by congr 1; exact D_restrict x a ha b hb
      _ = (sf b) |_ (N_opens x) := by apply restrict_restrict
  -- contruct a compatible family from N_opens and claim it is an inverse image of t
  have I_non_empty : ∀ x, ∃ a, a ∈ I x := by
    intro x
    rcases Set.iUnion_eq_univ_iff.mp W_cover x with ⟨a, ha⟩
    use a, subset_closure ha
  choose a_chosen a_chosen_mem using fun x => I_non_empty x
  let s_on_N : (x : X) → CC (F.obj (op (N_opens x))) := fun x =>
    (sf (a_chosen x)) |_ₗ (N_opens x) ⟪N_le_U x (a_chosen x) (a_chosen_mem x)⟫
  have : F.IsCompatible N_opens s_on_N := by
    intro x y
    let Nxy := N_opens x ⊓ N_opens y
    change s_on_N x |_ Nxy = s_on_N y |_ Nxy
    by_cases h : Nxy = ⊥
    · rw! [h]
      apply subsingleton_on_bot.elim
    simp_rw [← Opens.coe_eq_empty, ← Set.nonempty_iff_ne_empty] at h
    choose z hz using h
    choose a ha using I_non_empty z
    rw [SetLike.mem_coe, Opens.mem_inf] at hz
    have a_mem_Ix := (N_I_le x z hz.1) ha
    have a_mem_Iy := (N_I_le y z hz.2) ha
    have : N_opens x ≤ ⟨U (a_chosen x), U_open (a_chosen x)⟩ :=
      N_le_U x (a_chosen x) (a_chosen_mem x)
    have : N_opens x ≤ ⟨U a, U_open a⟩ := N_le_U x a a_mem_Ix
    have : N_opens y ≤ ⟨U a, U_open a⟩ := N_le_U y a a_mem_Iy
    have : N_opens y ≤ ⟨U (a_chosen y), U_open (a_chosen y)⟩ :=
      N_le_U y (a_chosen y) (a_chosen_mem y)
    calc
      (s_on_N x |_ Nxy) = (sf (a_chosen x)) |_ Nxy := by apply restrict_restrict
      _ = ((sf (a_chosen x)) |_ (N_opens x)) |_ Nxy := by symm; apply restrict_restrict
      _ = ((sf a) |_ (N_opens x)) |_ Nxy := by
        congr 1
        exact N_s_agree _ _ (a_chosen_mem x) _ a_mem_Ix
      _ = (sf a) |_ Nxy := by apply restrict_restrict
      _ = ((sf a) |_ (N_opens y)) |_ Nxy := by symm; apply restrict_restrict
      _ = ((sf (a_chosen y)) |_ (N_opens y)) |_ Nxy := by
        congr 1; symm
        exact N_s_agree _ _ (a_chosen_mem y) _ a_mem_Iy
      _ = (sf (a_chosen y)) |_ Nxy := by apply restrict_restrict
      _ = (s_on_N y |_ Nxy) := by symm; apply restrict_restrict
  rcases (F_epipresheaf N_opens s_on_N this) with s_with_glueing
  simp only [IsGluing] at s_with_glueing
  rw! (castMode := all) [N_opens_sup] at s_with_glueing
  obtain ⟨s, s_glueing⟩ := s_with_glueing
  use s
  --  prove it is an inverse image of t
  have := Sheaf.eq_of_locally_eq (⟨sheafify F, sheafify_isSheaf F⟩) N_opens
  rw! (castMode := all) [N_opens_sup] at this
  apply this (((toSheafify F).app (op ⊤)) s) t
  intro x
  change (((toSheafify F).app (op ⊤)) s) |_ (N_opens x) = t |_ (N_opens x)
  have : N_opens x ≤ ⟨U (a_chosen x), U_open _⟩ := N_le_U x (a_chosen x) (a_chosen_mem x)
  calc
    _ = ((toSheafify F).app (op (N_opens x))) (s |_ (N_opens x)) := (map_restrict _ _ _).symm
    _ = ((toSheafify F).app (op (N_opens x))) (s_on_N x) := by congr 1; apply s_glueing x
    _ = ((toSheafify F).app (op (N_opens x))) ((sf (a_chosen x)) |_ (N_opens x)) := by rfl
    _ = (((toSheafify F).app (op ⟨U (a_chosen x), U_open _⟩)) (sf (a_chosen x))) |_ (N_opens x) :=
      map_restrict _ _ _
    _ = (t |_ ⟨U (a_chosen x), U_open _⟩) |_ (N_opens x) := by
      congr 1; symm
      exact t_restrict (a_chosen x)
    _ = t |_ (N_opens x) := restrict_restrict _ _ _



end IsEpiPresheaf

end TheProofTemp

end Presheaf

end TopCat
