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
 * Expressions that work with any type. Use {@link hu.bme.mit.theta.core.type.anytype.Exprs} to
 * create them.
 * <p>
 * - {@link hu.bme.mit.theta.core.type.anytype.IteExpr}: conditional expression, e.g., if x &gt; 0
 * then x else -x - {@link hu.bme.mit.theta.core.type.anytype.PrimeExpr}: primed expression, e.g.,
 * x' - {@link hu.bme.mit.theta.core.type.anytype.RefExpr}: reference to a declaration, e.g., x
 */

package hu.bme.mit.theta.core.type.anytype;
