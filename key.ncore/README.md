# Design Documentation for NewCore

This file documents the changes to KeY's structure and the philosophy behind them. The general goal is to achieve 
language independence for KeY, i.e., to no longer have data structure suited _only_ for Java in the core. Anything 
Java-specific should be in a separate module.

## Changes (so far)

- Added `ncore` module; this stands for "new core" and contains language-independent structures for terms, formulas, 
etc.
  - Created `SyntaxElement` interface; used for both `LanguageElement` and `LogicElement`
  - Created `LanguageElement` interface; used for AST structure of target languages
  - Created `LogicElement` interface; currently only used for `Term`
    - Might be useful for splitting terms and formulas---if desired in the future
  - Created `Term` interface; intended to replace `core.Term`
  - Moved `Name`, `Named`, and `Sorted` to `ncore`
  - Created abstract, language-independent operator interfaces and abstract classes in `op`
    - `Modality` is changed to abstract class; must be implemented for each target language
  - Language-independent `Sort` and `AbstractSort`
    - No implementation of `Sort` in `ncore`
    - No concrete sorts (e.g., `ANY`, `FORMULA`)
  - `Modality` has a `kind` of type `ModalityKind`, i.e., box, diamond, etc.
  - `Modality` references program
- Changes to `core`
  - Removed dependency of `Operator` on `Term`
  - Created `ldt.JavaDLTheory`, which now holds `ANY`, `FORMULA`, etc. sorts
  - Classes and interfaces now depend on `ncore` structures
  - Removed `AbstractSort`; make `Sort` an abstract class and integrate old `AbstractSort` functionality
  - Move most `Term` methods to `ncore`
  - Move `Visitor` interface to `ncore`
  - Modality now references the program
  - Add `JavaModalityKind`
  - `Term` no longer has `javaBlock` field
  - Update matching and term creation
  - Modality has new equality
    - Equal iff kind and program are correct

## Philosophy

- **Anything** in `ncore` must be language-independent; **no** references to Java-specific things
- `core` depends on `ncore` and introduces Java-specifics

## Steps to Implement New Target Language

- Create new core for language
- Create specific sorts and DLTheory
- Create AST interfaces (how?)