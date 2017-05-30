package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static org.junit.Assert.assertEquals;

import java.util.Collections;

import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;

public class TreePredPrecTest {

	@Test
	public void test() {
		final IntLitExpr int0 = Int(0);
		final IntLitExpr int1 = Int(1);

		final VarDecl<IntType> va = Var("A", Types.Int());
		final VarDecl<IntType> vb = Var("B", Types.Int());
		final VarDecl<IntType> vc = Var("C", Types.Int());

		final Expr<BoolType> pa = Eq(va.getRef(), int1);
		final Expr<BoolType> pb = Eq(vb.getRef(), int1);
		final Expr<BoolType> pc = Eq(vc.getRef(), int1);

		final TreePredPrec prec = TreePredPrec.create(Collections.singletonList(pa));

		final Valuation v111 = Valuation.builder().put(va, int1).put(vb, int1).put(vc, int1).build();
		final Valuation v011 = Valuation.builder().put(va, int0).put(vb, int1).put(vc, int1).build();
		final Valuation v101 = Valuation.builder().put(va, int1).put(vb, int0).put(vc, int1).build();

		final PredState ps0 = prec.createState(v011);
		final PredState ps1 = prec.createState(v111);
		System.out.println(ps0);
		System.out.println(ps1);
		System.out.println("-----");
		assertEquals(ImmutableSet.of(Not(pa)), ps0.getPreds());
		assertEquals(ImmutableSet.of(pa), ps1.getPreds());

		prec.refine(ps1, pb);

		final PredState ps0r = prec.createState(v011);
		final PredState ps11 = prec.createState(v111);
		final PredState ps10 = prec.createState(v101);
		System.out.println(ps0r);
		System.out.println(ps11);
		System.out.println(ps10);
		System.out.println("-----");

		assertEquals(ps0, ps0r);
		assertEquals(ImmutableSet.of(pa, pb), ps11.getPreds());
		assertEquals(ImmutableSet.of(pa, Not(pb)), ps10.getPreds());

		prec.refine(ps10, pc);
		final PredState ps0rr = prec.createState(v011);
		final PredState ps11r = prec.createState(v111);
		final PredState ps101 = prec.createState(v101);
		System.out.println(ps0rr);
		System.out.println(ps11r);
		System.out.println(ps101);
		System.out.println("-----");

		assertEquals(ps0, ps0rr);
		assertEquals(ps11, ps11r);
		assertEquals(ImmutableSet.of(pa, Not(pb), pc), ps101.getPreds());
	}

	@Test(expected = IllegalStateException.class)
	public void testException() {
		final TreePredPrec prec = TreePredPrec.create(ImmutableSet.of(Eq(Int(2), Int(4))));

		final PredState state = PredState.of(Eq(Int(0), Int(1)));

		prec.refine(state, True());

	}

}
