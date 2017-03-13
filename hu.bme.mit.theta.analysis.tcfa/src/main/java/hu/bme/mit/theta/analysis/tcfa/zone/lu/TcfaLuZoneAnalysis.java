package hu.bme.mit.theta.analysis.tcfa.zone.lu;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.zone.ZonePrec;

public final class TcfaLuZoneAnalysis implements Analysis<LuZoneState, TcfaAction, ZonePrec> {
	private static final TcfaLuZoneAnalysis INSTANCE = new TcfaLuZoneAnalysis();

	private TcfaLuZoneAnalysis() {
	}

	public static TcfaLuZoneAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public Domain<LuZoneState> getDomain() {
		return LuZoneDomain.getInstance();
	}

	@Override
	public InitFunction<LuZoneState, ZonePrec> getInitFunction() {
		return TcfaLuZoneInitFunction.getInstance();
	}

	@Override
	public TransferFunction<LuZoneState, TcfaAction, ZonePrec> getTransferFunction() {
		return TcfaLuZoneTransferFunction.getInstance();
	}

}
