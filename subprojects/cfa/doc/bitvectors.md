# Bitvector support in Theta

As of now, Theta has basic bitvector support for the CFA formalism.

## Overview

In Theta, every bitvector has a length, and is either signed or unsigned. It follows, that the range of every bitvector has a size of 2<sup>n</sup>. There are different operations that are available for bitvectors. It is important to note, that only operations between bitvectors with the same size and signedness are valid.

Bitvectors have n bits. If the bitvector is unsigned then the values of the bits come from the binary representation of the underlying number. However, if the bitvector is signed then the values of the bits come from the two's complement representation of the underlying number.

## Declaring bitvector variables

To declare a bitvector variable, one has to specify the size and the signedness.

```
var x1 : bv[4] // Unsigned 4-bit-long bitvector
var x2 : bitvec[5] // Unsigned 5-bit-long bitvector

var u1 : ubv[4] // Unsigned 4-bit-long bitvector
var u2 : ubitvec[6] // Unsigned 6-bit-long bitvector

var s1 : sbv[4] // Signed 4-bit-long bitvector
var s2 : sbitvec[7] // Signed 7-bit-long bitvector

```

## Bitvector literals

There is a new literal, the bitvector literal that can be used to create bitvectors. Each literal defines the size and signedness of the literal. Moreover, eah literal can be entered using three different formats:

- The bitwise precise binary form
- The bitwise precise hexadecimal form
- And the non-bitwise-precise, although user-friendly decimal form

The two bitwise precise forms specify the value for all bits directly. These are useful for unsigned bitvectors, where there is no two's complement behavior (e.g. bitfields).

```
4'b0010 // Unsiged 4-bit-long bitvector literal (binary form)
8'xAF // Unsiged 4-bit-long bitvector literal (hexadecimal form)

4'bu0010 // Unsiged 4-bit-long bitvector literal (binary form)
8'xuAF // Unsiged 4-bit-long bitvector literal (hexadecimal form)

4'bs0010 // Signed 4-bit-long bitvector literal (binary form, not recommended)
8'xsAF // Signed 4-bit-long bitvector literal (hexadecimal form, not recommended)
```

The non-bitwise-precise decimal form can be used to create bitvectors that are based on numbers. Thsi form is recommended for signed bitvectors, or unsigned bitvectors that are not bitfields.

```
4'd10 // Unsigned 4-bit-long bitvector literal (decimal form)

4'du10 // Unsigned 4-bit-long bitvector literal (decimal form)

4'ds5 // Signed 4-bit-long bitvector literal (decimal form, positive value)
4'ds-5 // Signed 4-bit-long bitvector literal (decimal form, negative value)
```

## Operations on bitvectors

The following operations are defined on bitvectors. As a general rule, every binary operation requires the bitvector on the left hand side and the bitvector on the right hand side to have the same size and signedness.

The operators and their precedence are based on the [operators in C langauge](https://en.cppreference.com/w/c/language/operator_precedence).

### Basic arithmetic operations

These operations perform basic arithmetic operations on bitvectors. These operations require that the bitvector on the left hand side and the bitvector on the right hand side have the same size and signedness. These operations overflow!

- **Addition:** Adds two bitvectors; `a + b`
- **Subtraction:** Subtracts a from b; `a - b`
- **Multiplication:** Multiplies two bitvectors; `a * b`
- **Integer division:** Divides two bitvectors, and takes the integer part of the result; `a / b`
- **Modulo:** Calculates (a mod b); `a mod b`
- **Remainder:** Calculates the remainder of a / b; `a rem b`
- **Negate:** Negates the value of a (only valid for signed bitvectors); `-a`

### Bitvector specific operations

These operations are specific to bitvectors only. These operations require that the bitvector on the left hand side and the bitvector on the right hand side have the same size and signedness. For the exact semantics check out the respective operators in C. These operations overflow!

- **Bitwise and**: Ands two bitvectors; `a & b`
- **Bitwise or**: Ors two bitvectors; `a | b`
- **Bitwise xor**: XORs two bitvectors; `a ^ b`
- **Bitwise shift left**: Shifts *a* to the left with *b*; `a << b`
- **Bitwise arithmetic shift right**: Shifts *a* arithmetically to the right with *b*; `a >> b`
- **Bitwise logical shift right**: Shifts *a* logically to the right with *b*; `a >>> b`
- **Bitwise rotate left**: Rotates *a* to the left with *b*; `a <<~ b`
- **Bitwise rotate right**: Rotates *a* to the right with *b*; `a ~>> b`
- **Bitwise not:** Negates all the bits in bitvectors; `~a`

### Relational operations

These operations encode relational operations between bitvectors. These operations require that the bitvector on the left hand side and the bitvector on the right hand side have the same size and signedness.

- **Equality**: Checks if a equals to b; `a = b`
- **Non-equality**: Checks if a does not equal to b; `a /= b`
- **Greater than or equals to**: Checks if a is greater than or equals to b; `a >= b`
- **Greater than**: Checks if a is greater than b; `a > b`
- **Less than or equals to**: Checks if a is less than or equals to b; `a <= b`
- **Less than**: Checks if a is less than b; `a < b`

### Conversion "operations"

Bitvectors can be converted to integers, and vice-versa. However, since integers can have an arbitrily huge value, should that value be impossible to be represented in the bitvectors range, an exception will be thrown. So procede with caution!

There is no explicit conversion operator, however, the assignment statement converts between the two types.

```
var bv1 : bv[4]
var i1 : int

// ...

L0 -> L1 {
    bv1 := i1
    i1 := bv1
}
```

## Algorithmic support for verification with bitvectors

As of now, bitvectors are only partially supported due to the fact, that the underlying SMT solver, Z3 does not support interpolation when bitvectors are involved.

As a result, CEGAR with predicate abstraction is not supported at all. However, CEGAR with explicit value abstraction, and with the UNSAT core refinement strategy is working preoperty, as it does not rely on the interpolation capabilities of the SMT solver.
