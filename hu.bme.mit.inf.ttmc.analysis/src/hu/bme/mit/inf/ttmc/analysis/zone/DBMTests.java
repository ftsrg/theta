package hu.bme.mit.inf.ttmc.analysis.zone;

import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;

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

		final DBM dbm = DBM.zero(clocks).transform().up().free(x).reset(z, 3).up().build();

		System.out.println(dbm);
	}

}
