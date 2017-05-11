package hu.bme.mit.theta.formalism.tcfa.instances;

import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.formalism.ta.decl.impl.Decls2.Clock;

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

	public static TCFA fischer(final int n, final int k) {
		try {
			final InputStream inputStream = TcfaModels.class.getResourceAsStream("/fischer.tcfa");
			final TcfaSpec spec = TcfaDslManager.createTcfaSpec(inputStream, Int(k));
			final List<TCFA> tcfas = new ArrayList<>(n);

			for (int i = 1; i <= n; i++) {
				final Expr<RatType> x_i = Clock("x" + i).getRef();
				final TCFA fischer_i = spec.createTcfa("fischer", x_i, Int(i));
				tcfas.add(fischer_i);
			}

			final TCFA tcfa = NetworkTcfa.of(tcfas);
			return tcfa;

		} catch (final FileNotFoundException e) {
			throw new AssertionError();
		} catch (final IOException e) {
			throw new AssertionError();
		}
	}

	public static TCFA critRegion(final int n, final int a, final int b) {
		try {
			final InputStream inputStream = TcfaModels.class.getResourceAsStream("/critregion.tcfa");
			final TcfaSpec spec = TcfaDslManager.createTcfaSpec(inputStream, Int(a), Int(b));
			final List<TCFA> tcfas = new ArrayList<>(n);

			final TCFA counter = spec.createTcfa("counter", Int(n));
			tcfas.add(counter);

			for (int i = 1; i <= n; i++) {
				final Expr<RatType> x_i = Clock("x" + i).getRef();
				final TCFA cell_i = spec.createTcfa("cell", x_i, Int(i));
				tcfas.add(cell_i);
			}

			final TCFA tcfa = NetworkTcfa.of(tcfas);
			return tcfa;

		} catch (final FileNotFoundException e) {
			throw new AssertionError();
		} catch (final IOException e) {
			throw new AssertionError();
		}
	}

	public static TCFA lynch(final int n, final int t) {
		try {
			final InputStream inputStream = TcfaModels.class.getResourceAsStream("/lynch.tcfa");
			final TcfaSpec spec = TcfaDslManager.createTcfaSpec(inputStream, Int(t));
			final List<TCFA> tcfas = new ArrayList<>(n);

			for (int i = 1; i <= n; i++) {
				final Expr<RatType> x_i = Clock("x" + i).getRef();
				final TCFA process_i = spec.createTcfa("process", x_i, Int(i));
				tcfas.add(process_i);
			}

			final TCFA fischers = NetworkTcfa.of(tcfas);
			return fischers;

		} catch (final FileNotFoundException e) {
			throw new AssertionError();
		} catch (final IOException e) {
			throw new AssertionError();
		}
	}

	public static TCFA fddi(final int n, final int ttrt, final int sa) {
		try {
			final InputStream inputStream = TcfaModels.class.getResourceAsStream("/fddi.tcfa");
			final TcfaSpec spec = TcfaDslManager.createTcfaSpec(inputStream, Int(n), Int(ttrt), Int(sa));
			final List<TCFA> tcfas = new ArrayList<>(n);

			for (int i = 1; i <= n; i++) {
				final Expr<RatType> trt_i = Clock("trt" + i).getRef();
				final Expr<RatType> xa_i = Clock("xa" + i).getRef();
				final Expr<RatType> xb_i = Clock("xb" + i).getRef();
				final TCFA station_i = spec.createTcfa("station", trt_i, xa_i, xb_i, Int(i));
				tcfas.add(station_i);
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
