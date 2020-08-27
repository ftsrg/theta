/**
 * Bitvector type and its expressions. Use {@link hu.bme.mit.theta.core.type.bvtype.BvExprs} to create them.
 * Bitvectors can be used to simulate machine integers that can be signed/unsigned with a fixed range and
 * wraparound overflow semantics. For example, 255+1 on 8 unsigned bits will result in 0.
 *
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvType}: the actual bitvector type
 *
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvLitExpr}: bitvector literal
 *
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvNegExpr}: unary minus
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvPosExpr}: unary plus
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvAddExpr}: addition
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvSubExpr}: subtraction
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvMulExpr}: multiplication
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvDivExpr}: division
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvModExpr}: modulus
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvRemExpr}: remainder
 *
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvNotExpr}: bitwise not
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvAndExpr}: bitwise and
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvOrExpr}: bitwise or
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvXorExpr}: bitwise xor
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr}: shift left
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr}: arithmetic shift right
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr}: logical shift right
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr}: rotate left
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr}: rotate right
 *
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvEqExpr}: equal
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvNeqExpr}: not equal
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvGtExpr}: greater
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvLtExpr}: less
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvGeqExpr}: greater or equal
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvLeqExpr}: less or equal
 *
 * - {@link hu.bme.mit.theta.core.type.bvtype.BvToIntExpr}: cast to int
 */

package hu.bme.mit.theta.core.type.bvtype;