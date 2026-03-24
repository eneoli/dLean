-- This module serves as the root of the `DLean` library.
-- Import modules here that should be built as part of the library.

import DLean.Syntax.Syntax
import DLean.Semantics.Semantics
import DLean.USubst.Basic

-- import Lean
-- open Lean Meta

-- def countTheorems : MetaM Unit := do
--   let env ← getEnv
--   let mut count := 0

--   for (name, info) in env.constants.map₁ do
--     if let ConstantInfo.thmInfo _ := info then
--       if let some ranges ← findDeclarationRanges? name then
--         match env.getModuleIdxFor? name with
--         | none => count := count + 1
--         | some modIdx =>
--           let modName := env.header.moduleNames[modIdx.toNat]!
--           if modName.getRoot == `DLean then
--             IO.println name
--             count := count + 1

--   IO.println s!"Total theorems: {count}"

-- def countDefinitions : MetaM Unit := do
--   let env ← getEnv
--   let mut count := 0

--   for (name, info) in env.constants.map₁ do
--     if let ConstantInfo.defnInfo _ := info then
--       if let some ranges ← findDeclarationRanges? name then
--         if !name.isInternal &&
--            !name.isAuxLemma &&
--            !name.isImplementationDetail &&
--            !name.isInternalDetail &&
--            !name.isMetaprogramming then
--           match env.getModuleIdxFor? name with
--           | none => count := count + 1
--           | some modIdx =>
--             let modName := env.header.moduleNames[modIdx.toNat]!
--             if modName.getRoot == `DLean then
--               IO.println name
--               count := count + 1

--   IO.println s!"Total definitions: {count}"


-- #eval countTheorems
-- #eval countDefinitions
