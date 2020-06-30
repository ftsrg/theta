/**
 * This package contains types (e.g., Boolean, integer) and expressions
 * operating over them (e.g., Boolean connectives, arithmetic operations),
 * grouped into subpackages. Constructors of the types and expressions are
 * usually package private. Use the factory classes instead.
 *
 * - {@link hu.bme.mit.theta.core.type.Expr} is the main interface for expressions.
 *
 * - {@link hu.bme.mit.theta.core.type.anytype} and {@link hu.bme.mit.theta.core.type.abstracttype}
 *   are expressions for multiple types (e.g., conditional).
 * - {@link hu.bme.mit.theta.core.type.booltype} contains the Boolean type and expressions (e.g., and, or).
 * - {@link hu.bme.mit.theta.core.type.inttype} contains the mathematical (SMT) integer type and expressions
 *   (e.g., add, multiply).
 * - {@link hu.bme.mit.theta.core.type.rattype} contains the rational type and expression (e.g., division).
 * - {@link hu.bme.mit.theta.core.type.arraytype} contains the SMT array type (associative mapping from a
 *   key type to a value type) and expressions (e.g., read, write).
 * - {@link hu.bme.mit.theta.core.type.functype} contains the function type and expressions.
 */

package hu.bme.mit.theta.core.type;