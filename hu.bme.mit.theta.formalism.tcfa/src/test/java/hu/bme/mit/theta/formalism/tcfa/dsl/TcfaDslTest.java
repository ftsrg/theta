package hu.bme.mit.theta.formalism.tcfa.dsl;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslManager.createTcfaSpec;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.utils.TcfaVisualizer;

public class TcfaDslTest {

	@Test
	public void testFischer() throws FileNotFoundException, IOException {
		final Expr<IntType> lock = Var("lock", Int()).getRef();
		final Expr<RatType> x1 = Clock("x1").getRef();

		final TcfaSpec spec = createTcfaSpec("src/test/resources/fischer.tcfa", lock, Int(1), Int(2));
		final TCFA fischer = spec.createTcfa("fischer", x1, Int(1));
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(fischer)));
	}

	@Test
	public void testProsigma() throws FileNotFoundException, IOException {
		final TcfaSpec spec = createTcfaSpec("src/test/resources/prosigma.tcfa", Int(3), Int(7));
		final TCFA prosigma = spec.createTcfa("prosigma");
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(prosigma)));
	}

}
