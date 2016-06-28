package hu.bme.mit.inf.ttmc.analysis.zone;

import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs.Eq;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs.Leq;

import java.util.Set;

import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public class ZoneStateTests {

	@Test
	public void test() {
		final ClockDecl x = Clock("x");
		final ClockDecl y = Clock("y");
		final ClockDecl z = Clock("z");

		final Set<ClockDecl> clockDecls = ImmutableSet.of(x, y);

		final ZoneState z0 = ZoneState.top(clockDecls);
		System.out.println(z0);

		final ZoneState z1 = z0.transform().and(Leq(x, z, 0)).and(Eq(z, 4)).done();
		System.out.println(z1);

	}
}