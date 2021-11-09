package hu.bme.mit.theta.xcfa.analysis.common;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaAnalysis<S extends ExprState, A extends StmtAction, P extends Prec>
		implements Analysis<XcfaState<S>, A, XcfaPrec<P>> {

	private final PartialOrd<XcfaState<S>> partialOrd;
	private final InitFunc<XcfaState<S>, XcfaPrec<P>> initFunc;
	private final TransFunc<XcfaState<S>, A, XcfaPrec<P>> transFunc;

	private XcfaAnalysis(final List<XcfaLocation> initLoc, PartialOrd<XcfaState<S>> partialOrd, InitFunc<XcfaState<S>, XcfaPrec<P>> initFunc, TransFunc<XcfaState<S>, A, XcfaPrec<P>> transFunc) {
		this.partialOrd = partialOrd;
		this.initFunc = initFunc;
		this.transFunc = transFunc;
		checkNotNull(initLoc);
	}

	public static <S extends ExprState, A extends StmtAction, P extends Prec> XcfaAnalysis<S, A, P> create(final List<XcfaLocation> initLoc, PartialOrd<XcfaState<S>> partialOrd, InitFunc<XcfaState<S>, XcfaPrec<P>> initFunc, TransFunc<XcfaState<S>, A, XcfaPrec<P>> transFunc) {
		return new XcfaAnalysis<>(initLoc, partialOrd, initFunc, transFunc);
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
	public TransFunc<XcfaState<S>, A, XcfaPrec<P>> getTransFunc() {
		return transFunc;
	}
}
