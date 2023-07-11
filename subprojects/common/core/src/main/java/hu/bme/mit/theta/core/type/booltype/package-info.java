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
 * Bool type and its expressions. Use {@link hu.bme.mit.theta.core.type.booltype.BoolExprs} to
 * create them.
 * <p>
 * - {@link hu.bme.mit.theta.core.type.booltype.BoolType}: the actual Boolean type
 * <p>
 * - {@link hu.bme.mit.theta.core.type.booltype.TrueExpr}: true literal -
 * {@link hu.bme.mit.theta.core.type.booltype.FalseExpr}: false literal
 * <p>
 * - {@link hu.bme.mit.theta.core.type.booltype.NotExpr}: negation -
 * {@link hu.bme.mit.theta.core.type.booltype.AndExpr}: and (conjunction) -
 * {@link hu.bme.mit.theta.core.type.booltype.OrExpr}: or (disjunction) -
 * {@link hu.bme.mit.theta.core.type.booltype.ImplyExpr}: implication -
 * {@link hu.bme.mit.theta.core.type.booltype.XorExpr}: exclusive or (xor) -
 * {@link hu.bme.mit.theta.core.type.booltype.IffExpr}: equivalence (if and only if)
 * <p>
 * - {@link hu.bme.mit.theta.core.type.booltype.ExistsExpr}: existential quantifier -
 * {@link hu.bme.mit.theta.core.type.booltype.ForallExpr}: universal quantifier
 */

package hu.bme.mit.theta.core.type.booltype;