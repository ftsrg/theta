package hu.bme.mit.inf.ttmc.analysis.zone;

import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs.Leq;

import java.util.Set;

import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public class DBMTests {

	@Test
	public void test() {

		final ClockDecl x = Clock("x");
		final ClockDecl y = Clock("y");
		final ClockDecl z = Clock("z");

		final Set<ClockDecl> clocks = ImmutableSet.of(x, y, z);

		final DBM dbm = DBM.top(clocks);

		System.out.println(dbm);
	}

	@Test
	public void tesInterpolant() {
		final ClockDecl x1 = Clock("x1");
		final ClockDecl x2 = Clock("x2");
		final ClockDecl x3 = Clock("x3");
		final ClockDecl x4 = Clock("x4");
		final ClockDecl x5 = Clock("x5");

		final Set<ClockDecl> clocks = ImmutableSet.of(x1, x2, x3, x4, x5);

		final DBM dbmA = DBM.top(clocks);
		dbmA.and(Leq(x2, x1, 1));
		dbmA.and(Leq(x3, x2, 0));
		dbmA.and(Leq(x5, x4, -1));

		System.out.println(dbmA.getConstraints());

		final DBM dbmB = DBM.top(clocks);
		dbmB.and(Leq(x1, x5, 0));
		dbmB.and(Leq(x4, x3, -1));

		System.out.println(dbmB.getConstraints());

		final DBM interpolant = DBM.interpolant(dbmA, dbmB);
		System.out.println(interpolant.getConstraints());
	}
}
