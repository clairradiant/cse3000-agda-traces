# Infinite Traces for While in Agda

This repository contains code for the report "Stuck in a (While) Loop" produced as a part of CSE3000 Research Project at TU Delft.

The report can be found at LINK.

Created by Claire Stokka, contact: <claire@clairradiant.com>

Licensed under MIT

## Structure

- Language definitions, encodings of traces and related experiments are found in the "work" module
  - Language definitions are present in `Language.agda`.
  - Trace definitions are located in `MusicalTraces.agda`, `GuardedTraces.agda`, and `SizedTraces.agda`.
  - Relational semantics and experimentation for each trace type can be found in `BigRel.agda` through `BigRel4.agda`.
  - An implementation of functional semantics for the musical trace implementation can be found in `BigFunct.agda`.
- Additional examples for demonstrating limitations of coinduction in Agda are found in "examples".
- Literate Agda files used for typesetting in the report can be found in the "latex" module.

## Working with the Code

The project was developed using Agda 2.7.0.1 and agda-stdlib 2.2. The Dockerfile present in the repository defines an environment containing these versions of the tools. Additionally, a [devcontainer](https://containers.dev/) is defined which makes use of this Dockerfile and sets up the agda-mode extension for vscode. Launching the devcontainer within vscode allows for working with the project using the correct versions of Agda and agda-stdlib.
