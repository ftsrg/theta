package hu.bme.mit.theta.xcfa.analysis.declarative.noota;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.cat.solver.MemoryModel;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaDeclAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.prec.XcfaDeclPrec;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclAnalysis<S extends ExprState, P extends Prec>
		implements Analysis<XcfaDeclState<S>, XcfaDeclAction, XcfaDeclPrec<P>> {

	private final PartialOrd<XcfaDeclState<S>> partialOrd;
	private final InitFunc<XcfaDeclState<S>, XcfaDeclPrec<P>> initFunc;
	private final TransFunc<XcfaDeclState<S>, XcfaDeclAction, XcfaDeclPrec<P>> transFunc;

	private XcfaDeclAnalysis(final XcfaLocation initLoc, final MemoryModel memoryModel, final Analysis<S, ? super XcfaDeclAction, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		partialOrd = XcfaDeclOrd.create(analysis.getPartialOrd());
		initFunc = XcfaDeclInitFunc.create(initLoc, memoryModel, analysis.getInitFunc());
		transFunc = XcfaDeclTransFunc.create(analysis.getTransFunc());
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclAnalysis<S, P> create(final XcfaLocation initLoc, final MemoryModel memoryModel, final Analysis<S, ? super XcfaDeclAction, ? super P> analysis) {
		return new XcfaDeclAnalysis<>(initLoc, memoryModel, analysis);
	}

	@Override
	public PartialOrd<XcfaDeclState<S>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<XcfaDeclState<S>, XcfaDeclPrec<P>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XcfaDeclState<S>, XcfaDeclAction, XcfaDeclPrec<P>> getTransFunc() {
		return transFunc;
	}
}
