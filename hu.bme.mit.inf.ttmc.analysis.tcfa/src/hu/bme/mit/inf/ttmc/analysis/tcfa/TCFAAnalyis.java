package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAAnalyis<S extends State, P extends Precision> implements Analysis<TCFAState<S>, TCFAAction, P> {

	private final Domain<TCFAState<S>> domain;
	private final InitFunction<TCFAState<S>, P> initFunction;
	private final TransferFunction<TCFAState<S>, TCFAAction, P> transferFunction;

	public TCFAAnalyis(final TCFALoc initLoc, final Analysis<S, TCFAAction, P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		domain = new TCFADomain<>(analysis.getDomain());
		initFunction = new TCFAInitFunction<>(initLoc, analysis.getInitFunction());
		transferFunction = new TCFATransferFunction<>(analysis.getTransferFunction());
	}

	@Override
	public Domain<TCFAState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<TCFAState<S>, P> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<TCFAState<S>, TCFAAction, P> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super TCFAState<S>, ? extends TCFAAction> getActionFunction() {
		return TCFAActionFunction.getInstance();
	}

}
