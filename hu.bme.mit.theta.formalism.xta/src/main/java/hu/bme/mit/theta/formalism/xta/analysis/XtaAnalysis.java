package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaAnalysis<S extends State, P extends Prec> implements Analysis<XtaState<S>, XtaAction, P> {
	private final Domain<XtaState<S>> domain;
	private final InitFunc<XtaState<S>, P> initFunc;
	private final TransferFunc<XtaState<S>, XtaAction, P> transferFunc;

	private XtaAnalysis(final XtaSystem system, final Analysis<S, ? super XtaAction, ? super P> analysis) {
		checkNotNull(system);
		checkNotNull(analysis);
		domain = XtaDomain.create(analysis.getDomain());
		initFunc = XtaInitFunc.create(system, analysis.getInitFunc());
		transferFunc = XtaTransferFunc.create(analysis.getTransferFunc());
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
	public InitFunc<XtaState<S>, P> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<XtaState<S>, XtaAction, P> getTransferFunc() {
		return transferFunc;
	}

}
