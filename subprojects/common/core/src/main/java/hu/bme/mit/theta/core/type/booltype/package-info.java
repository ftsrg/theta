/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
 *
 * <p>- {@link hu.bme.mit.theta.core.type.booltype.BoolType}: the actual Boolean type
 *
 * <p>- {@link hu.bme.mit.theta.core.type.TrueExpr}: true literal - {@link
 * hu.bme.mit.theta.core.type.FalseExpr}: false literal
 *
 * <p>- {@link hu.bme.mit.theta.core.type.NotExpr}: negation - {@link
 * hu.bme.mit.theta.core.type.AndExpr}: and (conjunction) - {@link
 * hu.bme.mit.theta.core.type.OrExpr}: or (disjunction) - {@link
 * hu.bme.mit.theta.core.type.ImplyExpr}: implication - {@link hu.bme.mit.theta.core.type.XorExpr}:
 * exclusive or (xor) - {@link hu.bme.mit.theta.core.type.IffExpr}: equivalence (if and only if)
 *
 * <p>- {@link hu.bme.mit.theta.core.type.ExistsExpr}: existential quantifier - {@link
 * hu.bme.mit.theta.core.type.ForallExpr}: universal quantifier
 */
package hu.bme.mit.theta.core.type.booltype;
