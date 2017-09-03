package hu.bme.mit.theta.analysis.zone.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class LuZoneAnalysis<A extends Action> implements Analysis<LuZoneState, A, ZonePrec> {

	private final InitFunc<LuZoneState, ZonePrec> initFunc;
	private final TransferFunc<LuZoneState, A, ZonePrec> transferFunc;

	private LuZoneAnalysis(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		checkNotNull(analysis);
		initFunc = LuZoneInitFunc.create(analysis.getInitFunc());
		transferFunc = LuZoneTransferFunc.create(analysis.getTransferFunc());
	}

	public static <A extends Action> LuZoneAnalysis<A> create(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
		return new LuZoneAnalysis<>(analysis);
	}

	@Override
	public Domain<LuZoneState> getDomain() {
		return LuZoneDomain.getInstance();
	}

	@Override
	public InitFunc<LuZoneState, ZonePrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<LuZoneState, A, ZonePrec> getTransferFunc() {
		return transferFunc;
	}

}
