package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public class TcfaAnalyis<S extends State, P extends Precision> implements Analysis<TcfaState<S>, TcfaAction, P> {

	private final Domain<TcfaState<S>> domain;
	private final InitFunction<TcfaState<S>, P> initFunction;
	private final TransferFunction<TcfaState<S>, TcfaAction, P> transferFunction;

	public TcfaAnalyis(final TcfaLoc initLoc, final Analysis<S, TcfaAction, P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		domain = new TcfaDomain<>(analysis.getDomain());
		initFunction = new TcfaInitFunction<>(initLoc, analysis.getInitFunction());
		transferFunction = new TcfaTransferFunction<>(analysis.getTransferFunction());
	}

	@Override
	public Domain<TcfaState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<TcfaState<S>, P> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<TcfaState<S>, TcfaAction, P> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super TcfaState<S>, ? extends TcfaAction> getActionFunction() {
		return TcfaActionFunction.getInstance();
	}

}
