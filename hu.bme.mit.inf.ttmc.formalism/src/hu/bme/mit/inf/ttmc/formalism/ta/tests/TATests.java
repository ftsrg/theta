package hu.bme.mit.inf.ttmc.formalism.ta.tests;

import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.Constrs.And;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.Constrs.Clock;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.Constrs.Eq;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.Constrs.True;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Constr;

public class TATests {

	@Test
	public void testConstraints() {
		final Clock x = Clock("x");
		final Clock y = Clock("y");
		final Constr constr = And(Eq(x, y, 0), True(), Eq(y, x, 10));
		System.out.println(constr);
		System.out.println(constr.getClocks());
		System.out.println(constr.asExpr());

	}

}
