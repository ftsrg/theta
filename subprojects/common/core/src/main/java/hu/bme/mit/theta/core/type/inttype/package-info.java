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
 * Integer type and its expressions. Use {@link hu.bme.mit.theta.core.type.inttype.IntExprs} to
 * create them. Note that this is a (mathematical) SMT integer, with an unbounded range (long in the
 * implementation) and no overflows.
 * <p>
 * - {@link hu.bme.mit.theta.core.type.inttype.IntType}: the actual integer type.
 * <p>
 * - {@link hu.bme.mit.theta.core.type.inttype.IntLitExpr}: integer literal
 * <p>
 * - {@link hu.bme.mit.theta.core.type.inttype.IntNegExpr}: unary minus -
 * {@link hu.bme.mit.theta.core.type.inttype.IntPosExpr}: unary plus -
 * {@link hu.bme.mit.theta.core.type.inttype.IntAddExpr}: addition -
 * {@link hu.bme.mit.theta.core.type.inttype.IntSubExpr}: subtraction -
 * {@link hu.bme.mit.theta.core.type.inttype.IntMulExpr}: multiplication -
 * {@link hu.bme.mit.theta.core.type.inttype.IntDivExpr}: integer division -
 * {@link hu.bme.mit.theta.core.type.inttype.IntModExpr}: modulus -
 * {@link hu.bme.mit.theta.core.type.inttype.IntRemExpr}: remainder
 * <p>
 * - {@link hu.bme.mit.theta.core.type.inttype.IntEqExpr}: equal -
 * {@link hu.bme.mit.theta.core.type.inttype.IntNegExpr}: not equal -
 * {@link hu.bme.mit.theta.core.type.inttype.IntGtExpr}: greater -
 * {@link hu.bme.mit.theta.core.type.inttype.IntLtExpr}: less -
 * {@link hu.bme.mit.theta.core.type.inttype.IntGeqExpr}: greater or equal -
 * {@link hu.bme.mit.theta.core.type.inttype.IntLeqExpr}: less or equal
 * <p>
 * - {@link hu.bme.mit.theta.core.type.inttype.IntToRatExpr}: cast to rational
 */

package hu.bme.mit.theta.core.type.inttype;