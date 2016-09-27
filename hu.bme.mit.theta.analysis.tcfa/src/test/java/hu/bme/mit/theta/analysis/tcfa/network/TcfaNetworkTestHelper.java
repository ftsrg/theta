package hu.bme.mit.theta.analysis.tcfa.network;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.tcfa.NetworkTcfa;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.instances.FischerTcfa;
import hu.bme.mit.theta.formalism.tcfa.instances.ProsigmaTcfa;

final class TcfaNetworkTestHelper {

	private TcfaNetworkTestHelper() {
	}

	public static TCFA prosigma() {
		final ProsigmaTcfa prosigma = new ProsigmaTcfa(3, 7);

		final TCFA eth = prosigma.getETH();
		final TCFA fieldLG = prosigma.getFieldLG();
		final TCFA controlLG = prosigma.getControlLG();
		final TCFA faultModel = prosigma.getFaultModel();

		final TCFA network = NetworkTcfa.of(eth, fieldLG, controlLG, faultModel);
		return network;
	}

	public static TCFA fischer(final int n, final VarDecl<IntType> vlock) {
		final List<TCFA> tcfas = new ArrayList<>(n);
		for (int i = 0; i < n; i++) {
			final TCFA fischer = new FischerTcfa(i + 1, 1, 2, vlock).getTCFA();
			tcfas.add(fischer);
		}
		final TCFA fischers = NetworkTcfa.of(tcfas);
		return fischers;
	}

}
