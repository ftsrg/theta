package hu.bme.mit.theta.analysis.tcfa.zone;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.zone.ZoneDomain;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class TcfaZoneAnalysis implements Analysis<ZoneState, TcfaAction, ZonePrecision> {

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
	public InitFunction<ZoneState, ZonePrecision> getInitFunction() {
		return TcfaZoneInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ZoneState, TcfaAction, ZonePrecision> getTransferFunction() {
		return TcfaZoneTransferFunction.getInstance();
	}

	@Override
	public ActionFunction<? super ZoneState, ? extends TcfaAction> getActionFunction() {
		throw new UnsupportedOperationException();
	}

}
