package hu.bme.mit.theta.analysis.tcfa.zone;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.zone.ZoneDomain;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class TcfaZoneAnalysis implements Analysis<ZoneState, TcfaAction, ZonePrec> {

	private static final TcfaZoneAnalysis INSTANCE = new TcfaZoneAnalysis();

	private TcfaZoneAnalysis() {
	}

	public static TcfaZoneAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public Domain<ZoneState> getDomain() {
		return ZoneDomain.getInstance();
	}

	@Override
	public InitFunction<ZoneState, ZonePrec> getInitFunction() {
		return TcfaZoneInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ZoneState, TcfaAction, ZonePrec> getTransferFunction() {
		return TcfaZoneTransferFunction.getInstance();
	}

}
