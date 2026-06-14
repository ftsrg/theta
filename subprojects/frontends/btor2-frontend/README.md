# BTOR2 Frontend for Verification

This subproject adds a BTOR2 frontend to Theta. It is designed to parse and transform BTOR2 files into a formal model for verification purposes.

## Features

The BTOR2 frontend supports the following features:

* Parsing of BTOR2 files
* Transformation of BTOR2 instructions into Theta's intermediate representation (XCFA)
* Support for basic operations, including logical, arithmetic, and relational operations
* Handling of state transitions and initialization

## Limitations, Known Bugs

The following limitations and known issues exist for the BTOR2 frontend:

* **Incomplete Language Support:** Currently lacks support for the BTOR2 array sort and associated operations (e.g., `read`, `write`), preventing the verification of designs that rely on memory modeling.
* **Missing Operators:** Specific arithmetic and bit-manipulation operators, such as overflow predicates (`saddo`, `uaddo`, etc.) and reduction operations (`redand`, `redor`, `redxor`), are not yet supported.
* **Limited Property Scope:** Verification is currently restricted to safety properties (`bad` states). Liveness properties (e.g., `justice`, `fairness`) and other temporal specifications remain unsupported.

## High-Level Process

The workflow to process a BTOR2 file is as follows:

1. Provide a valid BTOR2 file
2. **Parse and transform the BTOR2 file using this frontend**
3. Use the intermediate model (_IM_) to build a formal model for verification

## Structure of the _IM_

The _IM_ represents the parsed BTOR2 model and includes the following elements:

* **Btor2UnaryOperation**: Represents an operation taking a single operand (e.g., bitwise NOT, negation).
* **Btor2BinaryOperation**: Represents an operation taking two operands (e.g., addition, bitwise AND, logical XOR).
* **Btor2TernaryOperation**: Represents an operation taking three operands (typically an `ite` or "if-then-else" statement).
* **Btor2SliceOperation**: Represents an operation that extracts a specific, contiguous range of bits from a bit-vector.
* **Btor2ExtOperation**: Represents an operation that increases the width of a bit-vector (e.g., zero-extension or sign-extension).
* **Btor2Comparison**: Represents a relational operation that compares two values (e.g., equality, greater than, signed less than).
* **Btor2Boolean**: Represents a Boolean value, constant, or a specific 1-bit Boolean sort context.
* **Btor2BitvecSort**: Represents the type definition (sort) for a bit-vector, explicitly defining its bit-width.
* **Btor2Input**: Represents an input variable (a value provided by the environment at each step).
* **Btor2State**: Represents a state variable (a memory element like a register or flip-flop).
* **Btor2Init**: Represents the initial value or condition of a state variable at the beginning of execution.
* **Btor2Next**: Represents the transition function that defines the value of a state variable in the next clock cycle.
* **Btor2Bad**: Represents a safety property defining a "bad" state that the model checker must prove is unreachable.
* **Btor2Const**: Represents a hardcoded constant bit-vector or numerical value.

To map these elements to a formal model, the `hu.bme.mit.theta.btor2xcfa.Btor2XcfaBuilder` class can be used.
