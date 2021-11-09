package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaSTAnalysis<S extends ExprState, P extends Prec>
		implements Analysis<XcfaSTState<S>, XcfaSTAction, XcfaSTPrec<P>> {

	private final PartialOrd<XcfaSTState<S>> partialOrd;
	private final InitFunc<XcfaSTState<S>, XcfaSTPrec<P>> initFunc;
	private final TransFunc<XcfaSTState<S>, XcfaSTAction, XcfaSTPrec<P>> transFunc;

	private XcfaSTAnalysis(final XcfaLocation initLoc, final Analysis<S, ? super XcfaSTAction, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		partialOrd = XcfaSTOrd.create(analysis.getPartialOrd());
		initFunc = XcfaSTInitFunc.create(initLoc, analysis.getInitFunc());
		transFunc = XcfaSTTransFunc.create(analysis.getTransFunc());
	}

	public static <S extends ExprState, P extends Prec> XcfaSTAnalysis<S, P> create(final XcfaLocation initLoc, final Analysis<S, ? super XcfaSTAction, ? super P> analysis) {
		return new XcfaSTAnalysis<>(initLoc, analysis);
	}

	@Override
	public PartialOrd<XcfaSTState<S>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<XcfaSTState<S>, XcfaSTPrec<P>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XcfaSTState<S>, XcfaSTAction, XcfaSTPrec<P>> getTransFunc() {
		return transFunc;
	}
}
