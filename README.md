# Formalizing a subset of GodotScript
A project for EPFL Programming Language Foundations course (CS-462).

This project formalizes a subset of GDScript, the scripting language of the Godot game engine, using the Rocq proof assistant, with a focus on its event-driven signal system (awaiting and emitting signals). \
We define a small-step operational semantics for program execution (a program corresponding to a set of classes running together). 

## Running the code
To run the code, you will need to have Rocq installed. You can find installation instructions on the [Rocq Website](https://rocq-prover.org/install).
We use version 9.1.0 of Rocq for this project.

With Rocq 9.1.0 installed, you can compile the project by running the following command in the project directory:

```bash
make rocq
```
### Description of the files:
- `GDS_Inductive.v`: Contains the inductive definitions of the syntax and semantics of the GDScript subset.
- `GDS_Solving.v`: Contains tactics and lemmas to prove examples of GDScript programs.
- `GDS_Examples.v`: Contains examples of GDScript programs and their proofs.
- `Type_System.v`: Will contain the type system for the GDScript subset, including typing rules and lemmas about type safety.
