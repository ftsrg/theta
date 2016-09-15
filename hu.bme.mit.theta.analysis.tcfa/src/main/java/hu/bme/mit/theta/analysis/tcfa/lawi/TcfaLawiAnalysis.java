package hu.bme.mit.theta.analysis.tcfa.lawi;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;

public final class TcfaLawiAnalysis implements Analysis<TcfaLawiState, TcfaAction, NullPrecision> {

	@Override
	public Domain<TcfaLawiState> getDomain() {
		return TcfaLawiDomain.getInstance();
	}

	@Override
	public InitFunction<TcfaLawiState, NullPrecision> getInitFunction() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public TransferFunction<TcfaLawiState, TcfaAction, NullPrecision> getTransferFunction() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public ActionFunction<? super TcfaLawiState, ? extends TcfaAction> getActionFunction() {
		return TcfaLawiActionFunction.getInstance();
	}

}