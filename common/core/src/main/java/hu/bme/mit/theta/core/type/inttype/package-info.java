/**
 * Integer type and its expressions. Use {@link hu.bme.mit.theta.core.type.inttype.IntExprs} to create them.
 * Note that this is a (mathematical) SMT integer, with an unbounded range (long in the implementation) and
 * no overflows.
 *
 * - {@link hu.bme.mit.theta.core.type.inttype.IntType}: the actual integer type.
 *
 * - {@link hu.bme.mit.theta.core.type.inttype.IntLitExpr}: integer literal
 *
 * - {@link hu.bme.mit.theta.core.type.inttype.IntNegExpr}: unary minus
 * - {@link hu.bme.mit.theta.core.type.inttype.IntPosExpr}: unary plus
 * - {@link hu.bme.mit.theta.core.type.inttype.IntAddExpr}: addition
 * - {@link hu.bme.mit.theta.core.type.inttype.IntSubExpr}: subtraction
 * - {@link hu.bme.mit.theta.core.type.inttype.IntMulExpr}: multiplication
 * - {@link hu.bme.mit.theta.core.type.inttype.IntDivExpr}: integer division
 * - {@link hu.bme.mit.theta.core.type.inttype.IntModExpr}: modulus
 * - {@link hu.bme.mit.theta.core.type.inttype.IntRemExpr}: remainder
 *
 * - {@link hu.bme.mit.theta.core.type.inttype.IntEqExpr}: equal
 * - {@link hu.bme.mit.theta.core.type.inttype.IntNegExpr}: not equal
 * - {@link hu.bme.mit.theta.core.type.inttype.IntGtExpr}: greater
 * - {@link hu.bme.mit.theta.core.type.inttype.IntLtExpr}: less
 * - {@link hu.bme.mit.theta.core.type.inttype.IntGeqExpr}: greater or equal
 * - {@link hu.bme.mit.theta.core.type.inttype.IntLeqExpr}: less or equal
 *
 * - {@link hu.bme.mit.theta.core.type.inttype.IntToRatExpr}: cast to rational
 */

package hu.bme.mit.theta.core.type.inttype;