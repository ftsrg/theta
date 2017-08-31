package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public final class CfaAnalysis<S extends State, P extends Prec>
		implements Analysis<CfaState<S>, CfaAction, CfaPrec<P>> {

	private final Domain<CfaState<S>> domain;
	private final InitFunction<CfaState<S>, CfaPrec<P>> initFunction;
	private final TransferFunction<CfaState<S>, CfaAction, CfaPrec<P>> transferFunction;

	private CfaAnalysis(final Loc initLoc, final Analysis<S, ? super CfaAction, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		domain = CfaDomain.create(analysis.getDomain());
		initFunction = CfaInitFunction.create(initLoc, analysis.getInitFunction());
		transferFunction = CfaTransferFunction.create(analysis.getTransferFunction());
	}

	public static <S extends State, P extends Prec> CfaAnalysis<S, P> create(final Loc initLoc,
			final Analysis<S, ? super CfaAction, ? super P> analysis) {
		return new CfaAnalysis<>(initLoc, analysis);
	}

	@Override
	public Domain<CfaState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<CfaState<S>, CfaPrec<P>> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<CfaState<S>, CfaAction, CfaPrec<P>> getTransferFunction() {
		return transferFunction;
	}

}
