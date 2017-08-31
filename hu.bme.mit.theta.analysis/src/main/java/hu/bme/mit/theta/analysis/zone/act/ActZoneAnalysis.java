package hu.bme.mit.theta.analysis.zone.act;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class ActZoneAnalysis<A extends Action> implements Analysis<ActZoneState, A, ZonePrec> {

	private final InitFunction<ActZoneState, ZonePrec> initFunction;
	private final TransferFunction<ActZoneState, A, ZonePrec> transferFunction;

	private ActZoneAnalysis(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		checkNotNull(analysis);
		initFunction = ActZoneInitFunction.create(analysis.getInitFunction());
		transferFunction = ActZoneTransferFunction.create(analysis.getTransferFunction());
	}

	public static <A extends Action> ActZoneAnalysis<A> create(
			final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		return new ActZoneAnalysis<>(analysis);
	}

	@Override
	public Domain<ActZoneState> getDomain() {
		return ActZoneDomain.getInstance();
	}

	@Override
	public InitFunction<ActZoneState, ZonePrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ActZoneState, A, ZonePrec> getTransferFunction() {
		return transferFunction;
	}

}
