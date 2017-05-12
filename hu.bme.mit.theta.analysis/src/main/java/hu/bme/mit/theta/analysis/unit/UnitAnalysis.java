package hu.bme.mit.theta.analysis.unit;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;

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
	public InitFunction<UnitState, UnitPrec> getInitFunction() {
		return UnitInitFunction.getInstance();
	}

	@Override
	public TransferFunction<UnitState, Action, UnitPrec> getTransferFunction() {
		return UnitTransferFunction.getInstance();
	}

}
