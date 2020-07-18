/**
 * Expressions that work with multiple types. Use {@link hu.bme.mit.theta.core.type.abstracttype.AbstractExprs}
 * to create them. Note that these are abstract classes, and the corresponding expression for a given type will
 * be created (e.g., integer addition).
 *
 * Arithmetic:
 * - {@link hu.bme.mit.theta.core.type.abstracttype.AddExpr}: addition
 * - {@link hu.bme.mit.theta.core.type.abstracttype.DivExpr}: division
 * - {@link hu.bme.mit.theta.core.type.abstracttype.MulExpr}: multiplication
 * - {@link hu.bme.mit.theta.core.type.abstracttype.SubExpr}: subtraction
 *
 * Comparison:
 * - {@link hu.bme.mit.theta.core.type.abstracttype.EqExpr}: equal
 * - {@link hu.bme.mit.theta.core.type.abstracttype.GeqExpr}: greater or equal
 * - {@link hu.bme.mit.theta.core.type.abstracttype.GtExpr}: greater
 * - {@link hu.bme.mit.theta.core.type.abstracttype.LeqExpr}: less or equal
 * - {@link hu.bme.mit.theta.core.type.abstracttype.LtExpr}: less
 * - {@link hu.bme.mit.theta.core.type.abstracttype.NeqExpr}: not equal
 *
 * Other
 * - {@link hu.bme.mit.theta.core.type.abstracttype.CastExpr}: cast
 */

package hu.bme.mit.theta.core.type.abstracttype;