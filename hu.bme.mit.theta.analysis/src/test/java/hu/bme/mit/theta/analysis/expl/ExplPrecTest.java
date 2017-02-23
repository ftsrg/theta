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

public class ExplPrecTest {
	private final VarDecl<IntType> x = Decls.Var("x", Types.Int());
	private final VarDecl<IntType> y = Decls.Var("y", Types.Int());

	@Test
	public void testInstances() {
		final ExplPrec p1 = ExplPrec.create();
		final ExplPrec p2 = ExplPrec.create();
		final ExplPrec p3 = ExplPrec.create(Collections.emptySet());
		final ExplPrec p4 = ExplPrec.create(Collections.singleton(x));

		Assert.assertTrue(p1 == p2);
		Assert.assertTrue(p1 == p3);
		Assert.assertTrue(p1 != p4);
		Assert.assertTrue(p2 == p3);
		Assert.assertTrue(p2 != p4);
		Assert.assertTrue(p3 != p4);
	}

	@Test
	public void testMapping() {
		final ExplPrec prec = ExplPrec.create(Collections.singleton(x));
		final ExplState s1 = prec.createState(Valuation.builder().put(x, Exprs.Int(1)).put(y, Exprs.Int(2)).build());
		final ExplState s2 = prec.createState(Valuation.builder().put(y, Exprs.Int(2)).build());

		Assert.assertEquals(Valuation.builder().put(x, Exprs.Int(1)).build(), s1.getValuation());
		Assert.assertEquals(Valuation.builder().build(), s2.getValuation());
	}

	@Test
	public void testRefinement() {
		final ExplPrec px = ExplPrec.create(Collections.singleton(x));
		final ExplPrec py = ExplPrec.create(Collections.singleton(y));
		final ExplPrec pxy = ExplPrec.create(ImmutableSet.of(x, y));

		final ExplPrec r1 = px.join(px);
		final ExplPrec r2 = px.join(py);
		final ExplPrec r3 = px.join(pxy);

		Assert.assertTrue(r1 == px);
		Assert.assertTrue(r2 != px);
		Assert.assertTrue(r3 == pxy);

	}
}
