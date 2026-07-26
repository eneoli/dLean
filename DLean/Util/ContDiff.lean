import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

import DLean.Syntax.Definitions

open scoped ContDiff

universe u uE uF uG

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
         {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
         {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
         {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem contDiff_dep_app {g : E → F → 𝕜}
                         {f : E → F}
                         (hg : ContDiff 𝕜 ∞ (Function.uncurry g))
                         (hf : ContDiff 𝕜 ∞ f)
                         : ContDiff 𝕜 ∞ (fun args => g args (f args)) :=
  ContDiff.comp hg (ContDiff.prodMk contDiff_id hf)

theorem contDiff_g_of_contDiff_comp_of_rightInverse
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {s : F → E}
    (hgf : ContDiff ℝ ∞ (g ∘ f)) (hs : ContDiff ℝ ∞ s) (hfs : f ∘ s = id) :
    ContDiff ℝ ∞ g := by
      convert hgf.comp hs using 1 ; ext ; simp_all +decide [ funext_iff, ( · ∘ · ) ]
