package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.interleavings.XcfaAction;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclarativeAnalysis<S extends ExprState, P extends Prec>
		implements Analysis<XcfaDeclarativeState<S>, XcfaAction, XcfaDeclarativePrec<P>> {

	private final PartialOrd<XcfaDeclarativeState<S>> partialOrd;
	private final InitFunc<XcfaDeclarativeState<S>, XcfaDeclarativePrec<P>> initFunc;
	private final TransFunc<XcfaDeclarativeState<S>, XcfaAction, XcfaDeclarativePrec<P>> transFunc;

	private XcfaDeclarativeAnalysis(final List<XcfaLocation> initLoc, final Analysis<S, ? super XcfaAction, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		partialOrd = XcfaDeclarativeOrd.create(analysis.getPartialOrd());
		initFunc = XcfaDeclarativeInitFunc.create(initLoc, analysis.getInitFunc());
		transFunc = XcfaDeclarativeTransFunc.create(analysis.getTransFunc());
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclarativeAnalysis<S, P> create(final List<XcfaLocation> initLoc, final Analysis<S, ? super XcfaAction, ? super P> analysis) {
		return new XcfaDeclarativeAnalysis<>(initLoc, analysis);
	}

	@Override
	public PartialOrd<XcfaDeclarativeState<S>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<XcfaDeclarativeState<S>, XcfaDeclarativePrec<P>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XcfaDeclarativeState<S>, XcfaAction, XcfaDeclarativePrec<P>> getTransFunc() {
		return transFunc;
	}
}
