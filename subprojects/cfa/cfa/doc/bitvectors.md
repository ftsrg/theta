# Bitvector support in Theta

As of now, Theta has basic bitvector support for the CFA formalism.

## Overview

In Theta, every bitvector has a positive length. It follows, that the range of every bitvector has a size of 2<sup>n</sup>. There are different operations that are available for bitvectors. It is important to note, that (usually) only operations between bitvectors with the same size are valid.

Bitvectors have n bits. Interpreting the signedness (signed/unsigned) of bitvectors depend on the operations (e.g., signed greater vs unsigned greater). If the bitvector is interpreted as an unsigned number then the values of the bits are interpreted as the binary representation of the underlying number. However, if the bitvector is interpreted as a signed number then the values of the bits are interpreted as the two's complement representation of the underlying number.

## Declaring bitvector variables

To declare a bitvector variable, one has to specify the size.

```
var x1 : bv[4] // 4-bit-long bitvector
var x2 : bv[7] // 7-bit-long bitvector
```

## Bitvector literals

There is a new literal, the bitvector literal that can be used to create bitvectors. Each literal defines the size of the literal. Moreover, each literal can be entered using three different formats:

- The bitwise precise binary form
- The bitwise precise hexadecimal form
- And the non-bitwise-precise, although user-friendly decimal form

The two bitwise precise forms specify the value for all bits directly. These are useful for "unsigned" bitvectors, where there is no two's complement behavior (e.g. bitfields).

```
4'b0010 // 4-bit-long bitvector literal (binary form)
8'xAF // 8-bit-long bitvector literal (hexadecimal form)
```

The non-bitwise-precise decimal form can be used to create bitvectors that are based on numbers. This form is recommended for "signed" bitvectors, or "unsigned" bitvectors that are not bitfields.

```
4'd5 // 4-bit-long bitvector literal (decimal form, positive value)
4'd-5 // 4-bit-long bitvector literal (decimal form, negative value)
```

## Operations on bitvectors

The following operations are defined on bitvectors. As a general rule, every binary operation requires the bitvector on the left-hand side and the bitvector on the right-hand side to have the same size.

The operators and their precedence are based on the [operators in C langauge](https://en.cppreference.com/w/c/language/operator_precedence).

### Basic arithmetic operations

These operations perform basic arithmetic operations on bitvectors. These operations require that the bitvector on the left-hand side and the bitvector on the right-hand side have the same size. These operations overflow!

- **Addition:** Adds two bitvectors; `a bvadd b`
- **Subtraction:** Subtracts a from b; `a bvsub b`
- **Multiplication:** Multiplies two bitvectors; `a bvmul b`
- **Unsigned integer division:** Divides two bitvectors interpreted as unsigned numbers, and takes the integer part of the result; `a bvudiv b`
- **Signed integer division:** Divides two bitvectors interpreted as signed numbers, and takes the integer part of the result; `a bvsdiv b`
- **(Signed) Modulo:** Calculates (a mod b); `a bvsmod b`
- **Unsigned remainder:** Calculates the remainder of a / b interpreted as unsigned numbers; `a bvurem b`
- **Signed remainder:** Calculates the remainder of a / b interpreted as signed numbers; `a bvsrem b`
- **Negate:** Negates the value of a (only valid for signed bitvectors); `bvneg a`

### Bitvector specific operations

These operations are specific to bitvectors only. These operations require that the bitvector on the left-hand side and the bitvector on the right-hand side have the same size. For the exact semantics check out the respective operators in C. These operations overflow!

- **Bitwise and**: Ands two bitvectors; `a bvand b`
- **Bitwise or**: Ors two bitvectors; `a bvor b`
- **Bitwise xor**: XORs two bitvectors; `a bvxor b`
- **Bitwise shift left**: Shifts *a* to the left with *b*; `a bvshl b`
- **Bitwise arithmetic shift right**: Shifts *a* arithmetically to the right with *b*; `a bvashr b`
- **Bitwise logical shift right**: Shifts *a* logically to the right with *b*; `a bvlshr b`
- **Bitwise rotate left**: Rotates *a* to the left with *b*; `a bvrol b`
- **Bitwise rotate right**: Rotates *a* to the right with *b*; `a bvror b`
- **Bitwise not:** Negates all the bits in bitvectors; `bvnot a`

The following four operators are special operators specific to bitvectors.

- **Concatenation**: Concatenates two bitvectors. The bitvectors do not have to be the same size; `a ++ b`
- **Extraction**: Extracts a part of the bitvector. The indexes must be constant integer literals. Parameter from is interpreted as the starting index (with the least significant bit being 0), while parameter until is interpreted as the (exclusive) ending index (with the least significant bit being 0). The result is a bitvector of length _until-from_; `a[until:from]`
- **Zero extend**: Extends the size of the bitvector to size N. The new bits will have the value 0; `a bv_zero_extend bv[N]`
- **Sign extend**: Extends the size of the bitvector to size N. The new bits will have the value of the most significant bit of a; `a bv_sign_extend bv[N]`

### Relational operations

These operations encode relational operations between bitvectors. These operations require that the bitvector on the left-hand side and the bitvector on the right-hand side have the same size.

- **Equality**: Checks if a equals to b; `a = b`
- **Non-equality**: Checks if a does not equal to b; `a /= b`
- **Unsigned greater than or equals to**: Checks if a is greater than or equals to b (a and b are interpreted as unsigned numbers); `a bvuge b`
- **Unsigned greater than**: Checks if a is greater than b (a and b are interpreted as unsigned numbers); `a bvugt b`
- **Unsigned less than or equals to**: Checks if a is less than or equals to b (a and b are interpreted as unsigned numbers); `a bvule b`
- **Unsigned less than**: Checks if a is less than b (a and b are interpreted as unsigned numbers); `a bvult b`
- **Signed greater than or equals to**: Checks if a is greater than or equals to b (a and b are interpreted as signed numbers); `a bvsge b`
- **Signed greater than**: Checks if a is greater than b (a and b are interpreted as signed numbers); `a bvsgt b`
- **Signed less than or equals to**: Checks if a is less than or equals to b (a and b are interpreted as signed numbers); `a bvsle b`
- **Signed less than**: Checks if a is less than b (a and b are interpreted as signed numbers); `a bvslt b`

## Algorithmic support for verification with bitvectors

The CEGAR algorithms use Z3 as an SMT solver, which does not support interpolation when bitvectors are involved.
Therefore, refinement algorithms involving interpolation (`--refinement *_ITP`) do not work.
However, there are other refinement algorithms (e.g., `UNSAT_CORE`, `UCB` or `NWT_*`) that do not rely on interpolation and work for bitvectors as well.
