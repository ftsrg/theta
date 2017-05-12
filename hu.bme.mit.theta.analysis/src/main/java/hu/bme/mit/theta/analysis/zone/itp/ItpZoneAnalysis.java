package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class ItpZoneAnalysis<A extends Action> implements Analysis<ItpZoneState, A, ZonePrec> {

	private final InitFunction<ItpZoneState, ZonePrec> initFunction;
	private final TransferFunction<ItpZoneState, A, ZonePrec> transferFunction;

	private ItpZoneAnalysis(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		checkNotNull(analysis);
		initFunction = ItpZoneInitFunction.create(analysis.getInitFunction());
		transferFunction = ItpZoneTransferFunction.create(analysis.getTransferFunction());
	}

	public static <A extends Action> ItpZoneAnalysis<A> create(
			final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		return new ItpZoneAnalysis<>(analysis);
	}

	////

	@Override
	public Domain<ItpZoneState> getDomain() {
		return ItpZoneDomain.getInstance();
	}

	@Override
	public InitFunction<ItpZoneState, ZonePrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<ItpZoneState, A, ZonePrec> getTransferFunction() {
		return transferFunction;
	}

}
