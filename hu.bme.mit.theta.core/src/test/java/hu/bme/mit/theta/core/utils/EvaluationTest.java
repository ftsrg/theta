package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neg;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Add;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Div;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Eq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Geq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Gt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Leq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Lt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Mul;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Neg;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Sub;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class EvaluationTest {

	private final ConstDecl<IntType> ca = Const("a", Int());
	private final ConstDecl<IntType> cb = Const("b", Int());

	private final Expr<IntType> a = ca.getRef();
	private final Expr<IntType> b = cb.getRef();

	private static <ExprType extends Type> LitExpr<ExprType> evaluate(final Expr<ExprType> expr) {
		return expr.eval(BasicValuation.builder().build());
	}

	private static <ExprType extends Type> LitExpr<ExprType> evaluate(final Expr<ExprType> expr, final Valuation val) {
		return expr.eval(val);
	}

	@Test
	public void testNot() {
		Assert.assertEquals(False(), evaluate(Not(And(True(), True()))));
		Assert.assertEquals(True(), evaluate(Not(And(False(), True()))));
	}

	@Test
	public void testAnd() {
		Assert.assertEquals(False(), evaluate(And(True(), False(), True())));
		Assert.assertEquals(True(), evaluate(And(True(), True(), True())));
	}

	@Test
	public void testOr() {
		Assert.assertEquals(False(), evaluate(Or(False(), False(), False())));
		Assert.assertEquals(True(), evaluate(Or(False(), True(), False())));
	}

	@Test
	public void testImply() {
		Assert.assertEquals(True(), evaluate(Imply(False(), True())));
		Assert.assertEquals(True(), evaluate(Imply(True(), True())));
		Assert.assertEquals(False(), evaluate(Imply(True(), False())));
		Assert.assertEquals(True(), evaluate(Imply(False(), False())));
	}

	@Test
	public void testIff() {
		Assert.assertEquals(False(), evaluate(Iff(False(), True())));
		Assert.assertEquals(True(), evaluate(Iff(True(), True())));
		Assert.assertEquals(False(), evaluate(Iff(True(), False())));
		Assert.assertEquals(True(), evaluate(Iff(False(), False())));
	}

	@Test
	public void testEq() {
		Assert.assertEquals(True(), evaluate(Eq(Int(2), Int(2))));
		Assert.assertEquals(False(), evaluate(Eq(Int(2), Int(-2))));
		Assert.assertEquals(True(), evaluate(Eq(Rat(1, 2), Rat(1, 2))));
		Assert.assertEquals(False(), evaluate(Eq(Rat(1, 2), Rat(-1, 2))));
	}

	@Test
	public void testGeq() {
		Assert.assertEquals(True(), evaluate(Geq(Rat(8, 4), Rat(2, 1))));
		Assert.assertEquals(True(), evaluate(Geq(Rat(3, 4), Rat(2, 3))));
		Assert.assertEquals(True(), evaluate(Geq(Rat(9, 4), Rat(2, 1))));
		Assert.assertEquals(False(), evaluate(Geq(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testGt() {
		Assert.assertEquals(False(), evaluate(Gt(Rat(8, 4), Rat(2, 1))));
		Assert.assertEquals(True(), evaluate(Gt(Rat(3, 4), Rat(2, 3))));
		Assert.assertEquals(True(), evaluate(Gt(Rat(9, 4), Rat(2, 1))));
		Assert.assertEquals(False(), evaluate(Gt(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testLeq() {
		Assert.assertEquals(True(), evaluate(Leq(Rat(8, 4), Rat(2, 1))));
		Assert.assertEquals(True(), evaluate(Leq(Rat(2, 3), Rat(3, 4))));
		Assert.assertEquals(True(), evaluate(Leq(Rat(2, 1), Rat(9, 4))));
		Assert.assertEquals(False(), evaluate(Leq(Rat(9, 4), Rat(2, 1))));
	}

	@Test
	public void testLt() {
		Assert.assertEquals(False(), evaluate(Lt(Rat(2, 1), Rat(8, 4))));
		Assert.assertEquals(True(), evaluate(Lt(Rat(2, 3), Rat(3, 4))));
		Assert.assertEquals(True(), evaluate(Lt(Rat(2, 1), Rat(9, 4))));
		Assert.assertEquals(False(), evaluate(Lt(Rat(9, 4), Rat(2, 1))));
	}

	@Test
	public void testIntDiv() {
		Assert.assertEquals(Int(0), evaluate(Div(Int(1), Int(2))));
		Assert.assertEquals(Int(1), evaluate(Div(Int(3), Int(2))));
	}

	@Test
	public void testRatDiv() {
		Assert.assertEquals(Rat(8, 9), evaluate(Div(Rat(2, 3), Rat(3, 4))));
		Assert.assertEquals(Rat(1, 2), evaluate(Div(Rat(2, 3), Rat(4, 3))));
		Assert.assertEquals(Rat(1, 3), evaluate(Div(Rat(2, 3), Rat(2, 1))));
		Assert.assertEquals(Rat(1, 2), evaluate(Div(Rat(2, 1), Rat(4, 1))));
	}

	@Test
	public void testNeg() {
		Assert.assertEquals(Rat(1, 2), evaluate(Neg(Neg(Neg(Neg(Rat(1, 2)))))));
		Assert.assertEquals(Rat(-1, 2), evaluate(Neg(Neg(Neg(Neg(Neg(Rat(1, 2))))))));
		Assert.assertEquals(Int(182), evaluate(Neg(Neg(Neg(Neg(Int(182)))))));
		Assert.assertEquals(Int(-182), evaluate(Neg(Neg(Neg(Neg(Neg(Int(182))))))));
	}

	@Test
	public void testSub() {
		Assert.assertEquals(Int(-1), evaluate(Sub(Int(7), Int(8))));
		Assert.assertEquals(Rat(1, 4), evaluate(Sub(Rat(3, 4), Rat(1, 2))));
		Assert.assertEquals(Rat(-1, 4), evaluate(Sub(Rat(3, 4), Rat(1, 1))));
	}

	@Test
	public void testAdd() {
		Assert.assertEquals(Int(6), evaluate(Add(Int(1), Int(2), Int(3))));
		Assert.assertEquals(Int(0), evaluate(Add(Int(1), Int(2), Int(-3))));
		Assert.assertEquals(Rat(7, 12), evaluate(Add(Rat(1, 3), Rat(1, 4))));
	}

	@Test
	public void testMul() {
		Assert.assertEquals(Int(30), evaluate(Mul(Int(2), Int(3), Int(5))));
		Assert.assertEquals(Rat(1, 1), evaluate(Mul(Rat(2, 1), Rat(1, 1), Rat(1, 2))));
		Assert.assertEquals(Rat(3, 4), evaluate(Mul(Rat(3, 2), Rat(1, 1), Rat(1, 2))));
	}

	@Test
	public void testIte() {
		Assert.assertEquals(Int(1), evaluate(Ite(True(), Int(1), Int(2))));
		Assert.assertEquals(Int(2), evaluate(Ite(False(), Int(1), Int(2))));
		Assert.assertEquals(Int(1), evaluate(Ite(True(), Ite(True(), Ite(True(), Int(1), Int(2)), Int(3)), Int(4))));
	}

	@Test
	public void testModel() {
		final Valuation val = BasicValuation.builder().put(ca, Int(5)).put(cb, Int(10)).build();
		Assert.assertEquals(Int(15), evaluate(Add(a, b), val));
		Assert.assertEquals(Int(50), evaluate(Mul(a, b), val));
		Assert.assertEquals(Int(0), evaluate(Div(a, b), val));
	}

	@Test(expected = RuntimeException.class)
	public void testException() {
		evaluate(Add(a, Int(1)));
	}
}
