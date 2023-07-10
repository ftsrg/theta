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
 * SMT array type and its expressions. Use {@link hu.bme.mit.theta.core.type.arraytype.ArrayExprs}
 * to create them. SMT arrays are unbounded, associative mappings from a key type to a value type.
 * <p>
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayType}: the actual array type
 * <p>
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr}: array literal, e.g., [0 &lt;- 182, 1
 * &lt;- 41, default &lt;- 75] - {@link hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr}: array
 * init expression, e.g., [0 &lt;- 182, 1 &lt;- x, default &lt;- 75]
 * <p>
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr}: read array at an index, e.g., a[i]
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr}: write array at an index, e.g., a[i
 * &lt;- v], the result of write is a new array, where element i is v
 * <p>
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayEqExpr}: equal -
 * {@link hu.bme.mit.theta.core.type.arraytype.ArrayNeqExpr}: not equal
 */

package hu.bme.mit.theta.core.type.arraytype;
