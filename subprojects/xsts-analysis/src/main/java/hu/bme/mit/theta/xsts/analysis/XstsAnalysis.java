package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expr.ExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsAnalysis<S extends ExprState, P extends Prec>
		implements Analysis<XstsState<S>, XstsAction, P> {

	private final PartialOrd<XstsState<S>> partialOrd;
	private final InitFunc<XstsState<S>, P> initFunc;
	private final TransFunc<XstsState<S>, XstsAction, P> transFunc;

	private XstsAnalysis(final Analysis<S, ? super XstsAction, ? super P> analysis) {
		checkNotNull(analysis);
		partialOrd = XstsOrd.create(analysis.getPartialOrd());
		transFunc = XstsTransFunc.create(analysis.getTransFunc());
		initFunc = XstsInitFunc.create(analysis.getInitFunc());
	}

	public static <S extends ExprState, P extends Prec> XstsAnalysis<S, P> create(final Analysis<S, ? super XstsAction, ? super P> analysis) {
		return new XstsAnalysis<>(analysis);
	}

	@Override
	public PartialOrd<XstsState<S>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<XstsState<S>, P> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XstsState<S>, XstsAction, P> getTransFunc() {
		return transFunc;
	}
}
