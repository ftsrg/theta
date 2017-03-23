package hu.bme.mit.theta.analysis.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaAnalysis<S extends State, P extends Prec> implements Analysis<XtaState<S>, XtaAction, P> {
	private final Domain<XtaState<S>> domain;
	private final InitFunction<XtaState<S>, P> initFunction;
	private final TransferFunction<XtaState<S>, XtaAction, P> transferFunction;

	private XtaAnalysis(final XtaSystem system, final Analysis<S, ? super XtaAction, ? super P> analysis) {
		checkNotNull(system);
		checkNotNull(analysis);
		domain = XtaDomain.create(analysis.getDomain());
		initFunction = XtaInitFunction.create(system, analysis.getInitFunction());
		transferFunction = XtaTransferFunction.create(analysis.getTransferFunction());
	}

	public static <S extends State, P extends Prec> XtaAnalysis<S, P> create(final XtaSystem system,
			final Analysis<S, ? super XtaAction, ? super P> analysis) {
		return new XtaAnalysis<>(system, analysis);
	}

	@Override
	public Domain<XtaState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<XtaState<S>, P> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<XtaState<S>, XtaAction, P> getTransferFunction() {
		return transferFunction;
	}

}
