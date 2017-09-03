package hu.bme.mit.theta.analysis.unit;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;

public final class UnitAnalysis implements Analysis<UnitState, Action, UnitPrec> {

	private static final UnitAnalysis INSTANCE = new UnitAnalysis();

	private UnitAnalysis() {
	}

	public static UnitAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public Domain<UnitState> getDomain() {
		return UnitDomain.getInstance();
	}

	@Override
	public InitFunc<UnitState, UnitPrec> getInitFunc() {
		return UnitInitFunc.getInstance();
	}

	@Override
	public TransferFunc<UnitState, Action, UnitPrec> getTransferFunc() {
		return UnitTransferFunc.getInstance();
	}

}
