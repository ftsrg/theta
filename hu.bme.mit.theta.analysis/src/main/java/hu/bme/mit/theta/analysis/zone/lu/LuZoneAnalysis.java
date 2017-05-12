package hu.bme.mit.theta.analysis.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class LuZoneAnalysis<A extends Action> implements Analysis<LuZoneState, A, ZonePrec> {

	private final InitFunction<LuZoneState, ZonePrec> initFunction;
	private final TransferFunction<LuZoneState, A, ZonePrec> transferFunction;

	private LuZoneAnalysis(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		checkNotNull(analysis);
		initFunction = LuZoneInitFunction.create(analysis.getInitFunction());
		transferFunction = LuZoneTransferFunction.create(analysis.getTransferFunction());
	}

	public static <A extends Action> LuZoneAnalysis<A> create(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		return new LuZoneAnalysis<>(analysis);
	}

	@Override
	public Domain<LuZoneState> getDomain() {
		return LuZoneDomain.getInstance();
	}

	@Override
	public InitFunction<LuZoneState, ZonePrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<LuZoneState, A, ZonePrec> getTransferFunction() {
		return transferFunction;
	}

}
