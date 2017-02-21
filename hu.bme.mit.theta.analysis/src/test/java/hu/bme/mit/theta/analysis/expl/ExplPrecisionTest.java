package hu.bme.mit.theta.analysis.expl;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

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
	public void testInstances() {
		final ExplPrecision p1 = ExplPrecision.create();
		final ExplPrecision p2 = ExplPrecision.create();
		final ExplPrecision p3 = ExplPrecision.create(Collections.emptySet());
		final ExplPrecision p4 = ExplPrecision.create(Collections.singleton(x));

		Assert.assertTrue(p1 == p2);
		Assert.assertTrue(p1 == p3);
		Assert.assertTrue(p1 != p4);
		Assert.assertTrue(p2 == p3);
		Assert.assertTrue(p2 != p4);
		Assert.assertTrue(p3 != p4);
	}

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
		final ExplPrecision px = ExplPrecision.create(Collections.singleton(x));
		final ExplPrecision py = ExplPrecision.create(Collections.singleton(y));
		final ExplPrecision pxy = ExplPrecision.create(ImmutableSet.of(x, y));

		final ExplPrecision r1 = px.join(px);
		final ExplPrecision r2 = px.join(py);
		final ExplPrecision r3 = px.join(pxy);

		Assert.assertTrue(r1 == px);
		Assert.assertTrue(r2 != px);
		Assert.assertTrue(r3 == pxy);

	}
}
