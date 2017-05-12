package hu.bme.mit.theta.formalism.sts;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

/**
 * Interface for a Symbolic Transition System (STS). An STS consists of
 * variables, initial formula, invariant formula, transition relation and a
 * property.
 */
public interface STS {

	Collection<VarDecl<? extends Type>> getVars();

	Collection<Expr<? extends BoolType>> getInit();

	Collection<Expr<? extends BoolType>> getTrans();

	Expr<? extends BoolType> getProp();

	// Deprecated methods for splittingcegar
	@Deprecated
	Valuation getConcreteState(final Model model, final int i);

	@Deprecated
	Valuation getConcreteState(final Model model, final int i, final Collection<VarDecl<? extends Type>> variables);

	@Deprecated
	List<Valuation> extractTrace(final Model model, final int length);

	@Deprecated
	List<Valuation> extractTrace(final Model model, final int length,
			final Collection<VarDecl<? extends Type>> variables);
}
