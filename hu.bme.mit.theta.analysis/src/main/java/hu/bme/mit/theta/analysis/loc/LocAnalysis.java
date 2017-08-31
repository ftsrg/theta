package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

public final class LocAnalysis<S extends State, A extends LocAction, P extends Prec>
		implements Analysis<LocState<S>, A, LocPrec<P>> {

	private final Domain<LocState<S>> domain;
	private final InitFunction<LocState<S>, LocPrec<P>> initFunction;
	private final TransferFunction<LocState<S>, A, LocPrec<P>> transferFunction;

	private LocAnalysis(final CfaLoc initLoc, final Analysis<S, ? super A, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		domain = LocDomain.create(analysis.getDomain());
		initFunction = LocInitFunction.create(initLoc, analysis.getInitFunction());
		transferFunction = LocTransferFunction.create(analysis.getTransferFunction());
	}

	public static <S extends State, A extends LocAction, P extends Prec> LocAnalysis<S, A, P> create(
			final CfaLoc initLoc, final Analysis<S, ? super A, ? super P> analysis) {
		return new LocAnalysis<>(initLoc, analysis);
	}

	@Override
	public Domain<LocState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<LocState<S>, LocPrec<P>> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<LocState<S>, A, LocPrec<P>> getTransferFunction() {
		return transferFunction;
	}

}
