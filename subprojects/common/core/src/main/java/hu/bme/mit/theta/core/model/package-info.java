/**
 * This package contains different implementations of models that assign expressions or literals to declarations.
 * - {@link hu.bme.mit.theta.core.model.Substitution} is a substitution that maps expressions to declarations.
 *   - {@link hu.bme.mit.theta.core.model.BasicSubstitution} is a basic implementation of a substitution.
 *   - {@link hu.bme.mit.theta.core.model.NestedSubstitution} implements a scoped substitution.
 * - {@link hu.bme.mit.theta.core.model.Valuation} is a special case of {@link hu.bme.mit.theta.core.model.Substitution}
 *   where literal expressions are assigned to declarations.
 *   - {@link hu.bme.mit.theta.core.model.MutableValuation} implements a mutable valuation.
 *   - {@link hu.bme.mit.theta.core.model.ImmutableValuation} implements an immutable valuation.
 */

package hu.bme.mit.theta.core.model;