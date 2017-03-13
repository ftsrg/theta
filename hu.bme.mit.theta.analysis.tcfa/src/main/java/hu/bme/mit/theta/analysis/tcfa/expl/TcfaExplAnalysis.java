package hu.bme.mit.theta.analysis.tcfa.expl;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplDomain;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;

public final class TcfaExplAnalysis implements Analysis<ExplState, TcfaAction, ExplPrec> {

	private static final TcfaExplAnalysis INSTANCE = new TcfaExplAnalysis();

	private TcfaExplAnalysis() {
	}

	public static TcfaExplAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public Domain<ExplState> getDomain() {
		return ExplDomain.getInstance();
	}

	@Override
	public InitFunction<ExplState, ExplPrec> getInitFunction() {
		return TcfaExplInitFunction.getInstance();
	}

	@Override
	public TransferFunction<ExplState, TcfaAction, ExplPrec> getTransferFunction() {
		return TcfaExplTransferFunction.getInstance();
	}

}
