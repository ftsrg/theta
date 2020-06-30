/**
 * This package contains types (e.g., boolean, integer) and expressions
 * operating over them (e.g., boolean connectives, arithmetic operations),
 * grouped into subpackages. Constructors of the types and expressions are
 * usually package private. Use the factory classes instead.
 *
 * - {@link hu.bme.mit.theta.core.type.Expr} is the main interface for expressions.
 * - {@link hu.bme.mit.theta.core.type.anytype.Exprs} and {@link hu.bme.mit.theta.core.type.abstracttype.AbstractExprs}
 *   work for multiple types (e.g., conditional).
 * - {@link hu.bme.mit.theta.core.type.booltype.BoolExprs} can create Boolean type and expressions (e.g., and, or).
 * - {@link hu.bme.mit.theta.core.type.inttype.IntExprs} can create mathematical (SMT) integer type and expressions
 *   (e.g., add, multiply).
 * - {@link hu.bme.mit.theta.core.type.rattype.RatExprs} can create rational type and expression (e.g., division).
 * - {@link hu.bme.mit.theta.core.type.arraytype.ArrayExprs} can create SMT array type (associative mapping from a
 *   key type to a value type) and expressions (e.g., read, write).
 * - {@link hu.bme.mit.theta.core.type.functype.FuncExprs} can create function type and expressions.
 */

package hu.bme.mit.theta.core.type;