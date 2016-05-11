package hu.bme.mit.inf.ttmc.analysis.zone;

import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;

import java.util.Set;

import org.junit.Test;

import com.google.common.collect.ImmutableSortedSet;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public class ZoneStateTests {

	@Test
	public void test() {

		final ImmutableSortedSet.Builder<ClockDecl> builder = ImmutableSortedSet.naturalOrder();
		builder.add(Clock("z"));
		builder.add(Clock("x"));
		builder.add(Clock("y"));
		final Set<ClockDecl> clockDecls = builder.build();

		final ZoneState z0 = ZoneState.zero(clockDecls);
		System.out.println(z0);

		final ZoneState z1 = z0.up();
		System.out.println(z1);

	}

}
