/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.frontend.models

enum class Btor2IndexedOperator {
    SEXT,
    UEXT,
    SLICE
}

enum class Btor2UnaryOperator {
    NOT,
    INC,
    DEC,
    NEG,
    REDAND,
    REDOR,
    REDXOR
}

enum class Btor2ComparisonOperator {
    EQ,
    NEQ,
    SLT,
    SLTE,
    SGT,
    SGTE,
    ULT,
    ULTE,
    UGT,
    UGTE
}

enum class Btor2BooleanOperator {
    IFF,
    IMPLIES
}

enum class Btor2BinaryOperator {
    AND,
    NAND,
    NOR,
    OR,
    XOR,
    ADD,
    MUL,
    UDIV,
    UREM,
    SDIV,
    SREM,
    SMOD,
    CONCAT,
    SADDO,
    SDIVO,
    SMULO,
    SSUBO,
    UADDO,
    UMULO,
    USUBO,
    ROL,
    ROR,
    SLL,
    SRA,
    SRL,
    READ
}

enum class Btor2TernaryOperator {
    ITE,
    WRITE
}
