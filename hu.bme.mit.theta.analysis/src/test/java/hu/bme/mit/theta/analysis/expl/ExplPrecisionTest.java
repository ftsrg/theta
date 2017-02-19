package hu.bme.mit.theta.analysis.expl;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;

public class ExplPrecisionTest {
	private final VarDecl<IntType> x = Decls.Var("x", Types.Int());
	private final VarDecl<IntType> y = Decls.Var("y", Types.Int());

	@Test
	public void testMapping() {
		final ExplPrecision prec = ExplPrecision.create(Collections.singleton(x));
		final ExplState s1 = prec.createState(Valuation.builder().put(x, Exprs.Int(1)).put(y, Exprs.Int(2)).build());
		final ExplState s2 = prec.createState(Valuation.builder().put(y, Exprs.Int(2)).build());

		Assert.assertEquals(Valuation.builder().put(x, Exprs.Int(1)).build(), s1.getValuation());
		Assert.assertEquals(Valuation.builder().build(), s2.getValuation());
	}

	@Test
	public void testRefinement() {
		final ExplPrecision prec = ExplPrecision.create(Collections.singleton(x));
		final ExplPrecision r1 = prec.refine(x);
		final ExplPrecision r2 = prec.refine(y);

		Assert.assertTrue(r1 == prec);
		Assert.assertTrue(r2 != prec);

	}
}
