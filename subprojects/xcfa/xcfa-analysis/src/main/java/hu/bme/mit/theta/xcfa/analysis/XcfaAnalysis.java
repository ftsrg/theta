package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaAnalysis<S extends ExprState, P extends Prec>
		implements Analysis<XcfaState<S>, XcfaAction, XcfaPrec<P>> {

	private final PartialOrd<XcfaState<S>> partialOrd;
	private final InitFunc<XcfaState<S>, XcfaPrec<P>> initFunc;
	private final TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>> transFunc;

	private XcfaAnalysis(final Map<Integer, XcfaLocation> initLoc, final Analysis<S, ? super XcfaAction, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		partialOrd = XcfaOrd.create(analysis.getPartialOrd());
		initFunc = XcfaInitFunc.create(initLoc, analysis.getInitFunc());
		transFunc = XcfaTransFunc.create(analysis.getTransFunc());
	}

	public static <S extends ExprState, P extends Prec> XcfaAnalysis<S, P> create(final Map<Integer, XcfaLocation> initLoc, final Analysis<S, ? super XcfaAction, ? super P> analysis) {
		return new XcfaAnalysis<>(initLoc, analysis);
	}

	@Override
	public PartialOrd<XcfaState<S>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<XcfaState<S>, XcfaPrec<P>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>> getTransFunc() {
		return transFunc;
	}
}
