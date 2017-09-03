package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public final class CfaAnalysis<S extends ExprState, P extends Prec>
		implements Analysis<CfaState<S>, CfaAction, CfaPrec<P>> {

	private final Domain<CfaState<S>> domain;
	private final InitFunc<CfaState<S>, CfaPrec<P>> initFunc;
	private final TransferFunc<CfaState<S>, CfaAction, CfaPrec<P>> transferFunc;

	private CfaAnalysis(final Loc initLoc, final Analysis<S, ? super CfaAction, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		domain = CfaDomain.create(analysis.getDomain());
		initFunc = CfaInitFunc.create(initLoc, analysis.getInitFunc());
		transferFunc = CfaTransferFunc.create(analysis.getTransferFunc());
	}

	public static <S extends ExprState, P extends Prec> CfaAnalysis<S, P> create(final Loc initLoc,
			final Analysis<S, ? super CfaAction, ? super P> analysis) {
		return new CfaAnalysis<>(initLoc, analysis);
	}

	@Override
	public Domain<CfaState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<CfaState<S>, CfaPrec<P>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<CfaState<S>, CfaAction, CfaPrec<P>> getTransferFunc() {
		return transferFunc;
	}

}
