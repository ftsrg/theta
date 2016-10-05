package hu.bme.mit.theta.analysis.pred;

import static org.junit.Assert.assertEquals;

import java.util.Collections;

import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;

public class TreePredPrecisionTest {

	@Test
	public void test() {
		final IntLitExpr int0 = Exprs.Int(0);
		final IntLitExpr int1 = Exprs.Int(1);

		final VarDecl<IntType> va = Decls.Var("A", Types.Int());
		final VarDecl<IntType> vb = Decls.Var("B", Types.Int());
		final VarDecl<IntType> vc = Decls.Var("C", Types.Int());

		final Expr<BoolType> pa = Exprs.Eq(va.getRef(), int1);
		final Expr<BoolType> pb = Exprs.Eq(vb.getRef(), int1);
		final Expr<BoolType> pc = Exprs.Eq(vc.getRef(), int1);

		final TreePredPrecision prec = TreePredPrecision.create(Collections.singletonList(pa));

		final Valuation v111 = Valuation.builder().put(va, int1).put(vb, int1).put(vc, int1).build();
		final Valuation v011 = Valuation.builder().put(va, int0).put(vb, int1).put(vc, int1).build();
		final Valuation v101 = Valuation.builder().put(va, int1).put(vb, int0).put(vc, int1).build();

		final PredState ps0 = prec.mapToAbstractState(v011);
		final PredState ps1 = prec.mapToAbstractState(v111);
		System.out.println(ps0);
		System.out.println(ps1);
		System.out.println("-----");
		assertEquals(ImmutableSet.of(Exprs.Not(pa)), ps0.getPreds());
		assertEquals(ImmutableSet.of(pa), ps1.getPreds());

		prec.refine(ps1, pb);

		final PredState ps0r = prec.mapToAbstractState(v011);
		final PredState ps11 = prec.mapToAbstractState(v111);
		final PredState ps10 = prec.mapToAbstractState(v101);
		System.out.println(ps0r);
		System.out.println(ps11);
		System.out.println(ps10);
		System.out.println("-----");

		assertEquals(ps0, ps0r);
		assertEquals(ImmutableSet.of(pa, pb), ps11.getPreds());
		assertEquals(ImmutableSet.of(pa, Exprs.Not(pb)), ps10.getPreds());

		prec.refine(ps10, pc);
		final PredState ps0rr = prec.mapToAbstractState(v011);
		final PredState ps11r = prec.mapToAbstractState(v111);
		final PredState ps101 = prec.mapToAbstractState(v101);
		System.out.println(ps0rr);
		System.out.println(ps11r);
		System.out.println(ps101);
		System.out.println("-----");

		assertEquals(ps0, ps0rr);
		assertEquals(ps11, ps11r);
		assertEquals(ImmutableSet.of(pa, Exprs.Not(pb), pc), ps101.getPreds());
	}

	@Test(expected = IllegalStateException.class)
	public void testException() {
		final TreePredPrecision prec = TreePredPrecision.create(ImmutableSet.of(Exprs.Eq(Exprs.Int(2), Exprs.Int(4))));

		final PredState state = PredState.create(Exprs.Eq(Exprs.Int(0), Exprs.Int(1)));

		prec.refine(state, Exprs.True());

	}

}
