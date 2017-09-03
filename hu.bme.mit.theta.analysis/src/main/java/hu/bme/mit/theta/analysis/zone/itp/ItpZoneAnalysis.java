package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class ItpZoneAnalysis<A extends Action> implements Analysis<ItpZoneState, A, ZonePrec> {

	private final InitFunc<ItpZoneState, ZonePrec> initFunc;
	private final TransferFunc<ItpZoneState, A, ZonePrec> transferFunc;

	private ItpZoneAnalysis(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		checkNotNull(analysis);
		initFunc = ItpZoneInitFunc.create(analysis.getInitFunc());
		transferFunc = ItpZoneTransferFunc.create(analysis.getTransferFunc());
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
	public InitFunc<ItpZoneState, ZonePrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<ItpZoneState, A, ZonePrec> getTransferFunc() {
		return transferFunc;
	}

}
