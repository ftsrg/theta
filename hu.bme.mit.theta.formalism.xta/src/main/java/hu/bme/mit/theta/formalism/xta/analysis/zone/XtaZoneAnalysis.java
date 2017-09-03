package hu.bme.mit.theta.formalism.xta.analysis.zone;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZoneDomain;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;

public final class XtaZoneAnalysis implements Analysis<ZoneState, XtaAction, ZonePrec> {

	private static final XtaZoneAnalysis INSTANCE = new XtaZoneAnalysis();

	private XtaZoneAnalysis() {
	}

	public static XtaZoneAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public Domain<ZoneState> getDomain() {
		return ZoneDomain.getInstance();
	}

	@Override
	public InitFunc<ZoneState, ZonePrec> getInitFunc() {
		return XtaZoneInitFunc.getInstance();
	}

	@Override
	public TransferFunc<ZoneState, XtaAction, ZonePrec> getTransferFunc() {
		return XtaZoneTransferFunc.getInstance();
	}

}
