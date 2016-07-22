package hu.bme.mit.inf.ttmc.analysis.tcfa.pred;

import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.pred.PredDomain;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class TCFAPredAnalysis implements Analysis<PredState, TCFAAction, PredPrecision> {

	private final Domain<PredState> domain;
	private final TransferFunction<PredState, TCFAAction, PredPrecision> transferFunction;

	public TCFAPredAnalysis(final Solver solver) {
		domain = PredDomain.create(solver);
		transferFunction = new TCFAPredTransferFunction(solver);
	}

	@Override
	public Domain<PredState> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<PredState, PredPrecision> getInitFunction() {
		return TCFAPredInitFunction.getInstance();
	}

	@Override
	public TransferFunction<PredState, TCFAAction, PredPrecision> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super PredState, ? extends TCFAAction> getActionFunction() {
		throw new UnsupportedOperationException();
	}

}
