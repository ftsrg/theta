package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>> {

	private final TransFunc<S, ? super XcfaAction, ? super P> transFunc;

	private XcfaTransFunc(final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaTransFunc<S, P> create(final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		return new XcfaTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaState<S>> getSuccStates(XcfaState<S> state, XcfaAction action, XcfaPrec<P> prec) {
		return null;
	}
}
