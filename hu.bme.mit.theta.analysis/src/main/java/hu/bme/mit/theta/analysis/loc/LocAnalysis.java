package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.LTS;
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
	private final LTS<? super LocState<S, L, E>, ? extends A> actionFunction;

	private LocAnalysis(final L initLoc, final Analysis<S, ? super A, P> analysis,
			final Function<? super E, ? extends A> actionCreator) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		checkNotNull(actionCreator);
		domain = LocDomain.create(analysis.getDomain());
		initFunction = LocInitFunction.create(initLoc, analysis.getInitFunction());
		transferFunction = LocTransferFunction.create(analysis.getTransferFunction());
		actionFunction = LocActionFunction.create(actionCreator);
	}

	public static <S extends State, A extends LocAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocAnalysis<S, A, P, L, E> create(
			final L initLoc, final Analysis<S, ? super A, P> analysis,
			final Function<? super E, ? extends A> actionCreator) {
		return new LocAnalysis<>(initLoc, analysis, actionCreator);
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

	@Override
	public LTS<? super LocState<S, L, E>, ? extends A> getActionFunction() {
		return actionFunction;
	}

}
