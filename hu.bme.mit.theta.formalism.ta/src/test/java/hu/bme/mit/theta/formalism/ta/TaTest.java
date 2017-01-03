package hu.bme.mit.theta.formalism.ta;

import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.And;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.Eq;
import static hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs.True;
import static hu.bme.mit.theta.formalism.ta.decl.impl.Decls2.Clock;

import org.junit.Test;

import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.impl.MutableTa;

public class TaTest {

	@Test
	public void testConstraints() {
		final ClockDecl x = Clock("x");
		final ClockDecl y = Clock("y");
		final ClockConstr constr = And(Eq(x, y, 0), True(), Eq(y, x, 10));
		System.out.println(constr);
		System.out.println(constr.getClocks());
		System.out.println(constr.toExpr());

	}

	@Test
	public void testTA() {
		final MutableTa ta = new MutableTa();

		final ClockDecl x = Clock("x");
		final ClockDecl y = Clock("y");

		ta.addClock(x);
		ta.addClock(y);
		ta.createLoc(Eq(y, x, 10));

		System.out.println(ta.getClocks());
	}

}
