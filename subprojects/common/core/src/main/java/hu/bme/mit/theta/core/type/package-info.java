/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
/**
 * This package contains types (e.g., Boolean, integer) and expressions operating over them (e.g.,
 * Boolean connectives, arithmetic operations), grouped into subpackages. Constructors of the types
 * and expressions are usually package private. Use the factory classes instead.
 * <p>
 * - {@link hu.bme.mit.theta.core.type.Expr} is the main interface for expressions.
 * <p>
 * - {@link hu.bme.mit.theta.core.type.anytype} and {@link hu.bme.mit.theta.core.type.abstracttype}
 * are expressions for multiple types (e.g., conditional). -
 * {@link hu.bme.mit.theta.core.type.booltype} contains the Boolean type and expressions (e.g., and,
 * or). - {@link hu.bme.mit.theta.core.type.bvtype} contains the (SMT) bitvector type and
 * expressions (e.g., bitwise and, shifts). - {@link hu.bme.mit.theta.core.type.inttype} contains
 * the mathematical (SMT) integer type and expressions (e.g., add, multiply). -
 * {@link hu.bme.mit.theta.core.type.rattype} contains the rational type and expression (e.g.,
 * division). - {@link hu.bme.mit.theta.core.type.arraytype} contains the SMT array type
 * (associative mapping from a key type to a value type) and expressions (e.g., read, write). -
 * {@link hu.bme.mit.theta.core.type.functype} contains the function type and expressions.
 */

package hu.bme.mit.theta.core.type;