package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneDomain;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;

public class TCFAZoneAnalysis implements Analysis<ZoneState, TCFAAction, ZonePrecision> {

	private static final TCFAZoneAnalysis INSTANCE = new TCFAZoneAnalysis();

	private TCFAZoneAnalysis() {
		// TODO Auto-generated constructor stub
	}

	public static TCFAZoneAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public Domain<ZoneState> getDomain() {
		return ZoneDomain.getInstance();
	}

	@Override
	public InitFunction<ZoneState, ZonePrecision> getInitFunction() {
		return TCFAZoneInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ZoneState, TCFAAction, ZonePrecision> getTransferFunction() {
		return TCFAZoneTransferFunction.getInstance();
	}

}
