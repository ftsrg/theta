package hu.bme.mit.theta.analysis.tcfa.zone.itp;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;

public final class TcfaItpZoneAnalysis implements Analysis<ItpZoneState, TcfaAction, ZonePrecision> {

	private static final TcfaItpZoneAnalysis INSTANCE = new TcfaItpZoneAnalysis();

	private TcfaItpZoneAnalysis() {
	}

	public static TcfaItpZoneAnalysis getInstance() {
		return INSTANCE;
	}

	////

	@Override
	public Domain<ItpZoneState> getDomain() {
		return ItpZoneDomain.getInstance();
	}

	@Override
	public InitFunction<ItpZoneState, ZonePrecision> getInitFunction() {
		return TcfaItpZoneInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ItpZoneState, TcfaAction, ZonePrecision> getTransferFunction() {
		return TcfaItpZoneTransferFunction.getInstance();
	}

}
