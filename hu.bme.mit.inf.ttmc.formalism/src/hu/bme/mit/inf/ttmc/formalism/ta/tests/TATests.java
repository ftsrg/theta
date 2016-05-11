package hu.bme.mit.inf.ttmc.formalism.ta.tests;

import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs.And;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs.Eq;
import static hu.bme.mit.inf.ttmc.formalism.ta.constr.impl.ClockConstrs.True;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.impl.MutableTA;

public class TATests {

	@Test
	public void testConstraints() {
		final ClockDecl x = Clock("x");
		final ClockDecl y = Clock("y");
		final ClockConstr constr = And(Eq(x, y, 0), True(), Eq(y, x, 10));
		System.out.println(constr);
		System.out.println(constr.getClocks());
		System.out.println(constr.asExpr());

	}

	@Test
	public void testTA() {
		final MutableTA ta = new MutableTA();

		final ClockDecl x = Clock("x");
		final ClockDecl y = Clock("y");

		ta.addClock(x);
		ta.addClock(y);
		ta.createLoc(Eq(y, x, 10));

		System.out.println(ta.getClocks());
	}

}
