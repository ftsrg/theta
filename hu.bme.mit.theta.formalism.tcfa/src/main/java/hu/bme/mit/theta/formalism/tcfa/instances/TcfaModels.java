package hu.bme.mit.theta.formalism.tcfa.instances;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Clock;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.tcfa.NetworkTcfa;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslManager;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaSpec;

public final class TcfaModels {

	private TcfaModels() {
	}

	public static TCFA prosigma(final int tSync, final int tRtMax) {
		try {
			final InputStream inputStream = TcfaModels.class.getResourceAsStream("/prosigma.tcfa");
			final TcfaSpec spec = TcfaDslManager.createTcfaSpec(inputStream, Int(tSync), Int(tRtMax));
			final TCFA tcfa = spec.createTcfa("prosigma");
			return tcfa;

		} catch (final FileNotFoundException e) {
			throw new AssertionError();
		} catch (final IOException e) {
			throw new AssertionError();
		}
	}

	public static TCFA fischer(final int n, final int a, final int b) {
		try {
			final InputStream inputStream = TcfaModels.class.getResourceAsStream("/fischer.tcfa");
			final TcfaSpec spec = TcfaDslManager.createTcfaSpec(inputStream, Int(a), Int(b));
			final List<TCFA> tcfas = new ArrayList<>(n);

			for (int i = 1; i <= n; i++) {
				final Expr<RatType> x_i = Clock("x" + i).getRef();
				final TCFA fischer_i = spec.createTcfa("fischer", x_i, Int(i));
				tcfas.add(fischer_i);
			}

			final TCFA fischers = NetworkTcfa.of(tcfas);
			return fischers;

		} catch (final FileNotFoundException e) {
			throw new AssertionError();
		} catch (final IOException e) {
			throw new AssertionError();
		}
	}

}
