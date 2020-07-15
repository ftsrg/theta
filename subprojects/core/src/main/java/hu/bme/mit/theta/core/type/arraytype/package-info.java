/**
 * SMT array type and its expressions. Use {@link hu.bme.mit.theta.core.type.arraytype.ArrayExprs} to create them.
 * SMT arrays are unbounded, associative mappings from a key type to a value type.
 *
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayType}: the actual array type
 *
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr}: array literal, e.g., [0 <- 182, 1 <- 41, default <- 75]
 *
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr}: read array at an index, e.g., a[i]
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr}: write array at an index, e.g., a[i <- v],
 *   the result of write is a new array, where element i is v
 *
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayEqExpr}: equal
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayNeqExpr}: not equal
 */

package hu.bme.mit.theta.core.type.arraytype;