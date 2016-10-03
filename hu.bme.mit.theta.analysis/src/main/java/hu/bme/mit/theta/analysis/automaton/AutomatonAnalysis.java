package hu.bme.mit.theta.analysis.automaton;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class AutomatonAnalysis<S extends State, A extends AutomatonAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements Analysis<AutomatonState<S, L, E>, A, P> {

	private final Domain<AutomatonState<S, L, E>> domain;
	private final InitFunction<AutomatonState<S, L, E>, P> initFunction;
	private final TransferFunction<AutomatonState<S, L, E>, A, P> transferFunction;
	private final ActionFunction<? super AutomatonState<S, L, E>, ? extends A> actionFunction;

	private AutomatonAnalysis(final L initLoc, final Analysis<S, A, P> analysis,
			final Function<? super E, ? extends A> actionCreator) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		checkNotNull(actionCreator);
		domain = AutomatonDomain.create(analysis.getDomain());
		initFunction = AutomatonInitFunction.create(initLoc, analysis.getInitFunction());
		transferFunction = AutomatonTransferFunction.create(analysis.getTransferFunction());
		actionFunction = AutomatonActionFunction.create(actionCreator);
	}

	public static <S extends State, A extends AutomatonAction<L, E>, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> AutomatonAnalysis<S, A, P, L, E> create(
			final L initLoc, final Analysis<S, A, P> analysis, final Function<? super E, ? extends A> actionCreator) {
		return new AutomatonAnalysis<>(initLoc, analysis, actionCreator);
	}

	@Override
	public Domain<AutomatonState<S, L, E>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<AutomatonState<S, L, E>, P> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<AutomatonState<S, L, E>, A, P> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super AutomatonState<S, L, E>, ? extends A> getActionFunction() {
		return actionFunction;
	}

}
