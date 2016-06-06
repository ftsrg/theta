package hu.bme.mit.inf.ttmc.analysis.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.AnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class STSAnalysisContext implements
		AnalysisContext<State, Expr<? extends BoolType>, Expr<? extends BoolType>, Expr<? extends BoolType>> {

	final Expr<? extends BoolType> init;
	final Collection<Expr<? extends BoolType>> trans;
	final Expr<? extends BoolType> target;

	public STSAnalysisContext(final Expr<? extends BoolType> init, final Expr<? extends BoolType> trans,
			final Expr<? extends BoolType> target) {
		this.init = checkNotNull(init);
		this.trans = Collections.singleton(checkNotNull(trans));
		this.target = checkNotNull(target);
	}

	@Override
	public Expr<? extends BoolType> getInitialization() {
		return init;
	}

	@Override
	public Collection<? extends Expr<? extends BoolType>> getTransitions(final State state) {
		return trans;
	}

	@Override
	public Expr<? extends BoolType> getTarget() {
		return target;
	}

}
