package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class LocAnalysis<S extends State, A extends LocAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements Analysis<LocState<S, L, E>, A, LocPrecision<P, L, E>> {

	private final Domain<LocState<S, L, E>> domain;
	private final InitFunction<LocState<S, L, E>, LocPrecision<P, L, E>> initFunction;
	private final TransferFunction<LocState<S, L, E>, A, LocPrecision<P, L, E>> transferFunction;

	private LocAnalysis(final L initLoc, final Analysis<S, ? super A, P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		domain = LocDomain.create(analysis.getDomain());
		initFunction = LocInitFunction.create(initLoc, analysis.getInitFunction());
		transferFunction = LocTransferFunction.create(analysis.getTransferFunction());
	}

	public static <S extends State, A extends LocAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocAnalysis<S, A, P, L, E> create(
			final L initLoc, final Analysis<S, ? super A, P> analysis) {
		return new LocAnalysis<>(initLoc, analysis);
	}

	@Override
	public Domain<LocState<S, L, E>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<LocState<S, L, E>, LocPrecision<P, L, E>> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<LocState<S, L, E>, A, LocPrecision<P, L, E>> getTransferFunction() {
		return transferFunction;
	}

}
