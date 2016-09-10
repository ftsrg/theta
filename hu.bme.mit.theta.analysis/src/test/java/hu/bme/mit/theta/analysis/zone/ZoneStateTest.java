package hu.bme.mit.theta.analysis.zone;

import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.Eq;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.Leq;

import java.util.Set;

import org.junit.Ignore;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public class ZoneStateTest {

	@Test
	@Ignore
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