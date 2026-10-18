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
 * Rational type and its expressions. Use {@link hu.bme.mit.theta.core.type.rattype.RatExprs} to
 * create them.
 *
 * <p>- {@link hu.bme.mit.theta.core.type.rattype.RatType}: the actual rational type
 *
 * <p>- {@link hu.bme.mit.theta.core.type.RatLitExpr}: rational literal, e.g., 1%2 is 0.5
 *
 * <p>- {@link hu.bme.mit.theta.core.type.RatNegExpr}: unary minus - {@link
 * hu.bme.mit.theta.core.type.RatPosExpr}: unary plus - {@link
 * hu.bme.mit.theta.core.type.RatAddExpr}: addition - {@link hu.bme.mit.theta.core.type.RatSubExpr}:
 * subtraction - {@link hu.bme.mit.theta.core.type.RatMulExpr}: multiplication - {@link
 * hu.bme.mit.theta.core.type.RatDivExpr}: rational division
 *
 * <p>- {@link hu.bme.mit.theta.core.type.RatEqExpr}: equal - {@link
 * hu.bme.mit.theta.core.type.RatNeqExpr}: not equal - {@link hu.bme.mit.theta.core.type.RatGtExpr}:
 * greater - {@link hu.bme.mit.theta.core.type.RatLtExpr}: less - {@link
 * hu.bme.mit.theta.core.type.RatGeqExpr}: greater or equal - {@link
 * hu.bme.mit.theta.core.type.RatLeqExpr}: less or equal
 */
package hu.bme.mit.theta.core.type.rattype;
