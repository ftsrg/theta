package hu.bme.mit.theta.core.expr;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Xor;
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
import static org.junit.Assert.assertEquals;

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
		return expr.eval(BasicValuation.empty());
	}

	private static <ExprType extends Type> LitExpr<ExprType> evaluate(final Expr<ExprType> expr, final Valuation val) {
		return expr.eval(val);
	}

	@Test
	public void testNot() {
		assertEquals(False(), evaluate(Not(And(True(), True()))));
		assertEquals(True(), evaluate(Not(And(False(), True()))));
	}

	@Test
	public void testAnd() {
		assertEquals(False(), evaluate(And(True(), False(), True())));
		assertEquals(True(), evaluate(And(True(), True(), True())));
	}

	@Test
	public void testOr() {
		assertEquals(False(), evaluate(Or(False(), False(), False())));
		assertEquals(True(), evaluate(Or(False(), True(), False())));
	}

	@Test
	public void testImply() {
		assertEquals(True(), evaluate(Imply(False(), True())));
		assertEquals(True(), evaluate(Imply(True(), True())));
		assertEquals(False(), evaluate(Imply(True(), False())));
		assertEquals(True(), evaluate(Imply(False(), False())));
	}

	@Test
	public void testIff() {
		assertEquals(False(), evaluate(Iff(False(), True())));
		assertEquals(True(), evaluate(Iff(True(), True())));
		assertEquals(False(), evaluate(Iff(True(), False())));
		assertEquals(True(), evaluate(Iff(False(), False())));
	}

	@Test
	public void testXor() {
		assertEquals(True(), evaluate(Xor(False(), True())));
		assertEquals(False(), evaluate(Xor(True(), True())));
		assertEquals(True(), evaluate(Xor(True(), False())));
		assertEquals(False(), evaluate(Xor(False(), False())));
	}

	@Test
	public void testEq() {
		assertEquals(True(), evaluate(Eq(Int(2), Int(2))));
		assertEquals(False(), evaluate(Eq(Int(2), Int(-2))));
		assertEquals(True(), evaluate(Eq(Rat(1, 2), Rat(1, 2))));
		assertEquals(False(), evaluate(Eq(Rat(1, 2), Rat(-1, 2))));
	}

	@Test
	public void testGeq() {
		assertEquals(True(), evaluate(Geq(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), evaluate(Geq(Rat(3, 4), Rat(2, 3))));
		assertEquals(True(), evaluate(Geq(Rat(9, 4), Rat(2, 1))));
		assertEquals(False(), evaluate(Geq(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testGt() {
		assertEquals(False(), evaluate(Gt(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), evaluate(Gt(Rat(3, 4), Rat(2, 3))));
		assertEquals(True(), evaluate(Gt(Rat(9, 4), Rat(2, 1))));
		assertEquals(False(), evaluate(Gt(Rat(2, 1), Rat(9, 4))));
	}

	@Test
	public void testLeq() {
		assertEquals(True(), evaluate(Leq(Rat(8, 4), Rat(2, 1))));
		assertEquals(True(), evaluate(Leq(Rat(2, 3), Rat(3, 4))));
		assertEquals(True(), evaluate(Leq(Rat(2, 1), Rat(9, 4))));
		assertEquals(False(), evaluate(Leq(Rat(9, 4), Rat(2, 1))));
	}

	@Test
	public void testLt() {
		assertEquals(False(), evaluate(Lt(Rat(2, 1), Rat(8, 4))));
		assertEquals(True(), evaluate(Lt(Rat(2, 3), Rat(3, 4))));
		assertEquals(True(), evaluate(Lt(Rat(2, 1), Rat(9, 4))));
		assertEquals(False(), evaluate(Lt(Rat(9, 4), Rat(2, 1))));
	}

	@Test
	public void testIntDiv() {
		assertEquals(Int(0), evaluate(Div(Int(1), Int(2))));
		assertEquals(Int(1), evaluate(Div(Int(3), Int(2))));
	}

	@Test
	public void testRatDiv() {
		assertEquals(Rat(8, 9), evaluate(Div(Rat(2, 3), Rat(3, 4))));
		assertEquals(Rat(1, 2), evaluate(Div(Rat(2, 3), Rat(4, 3))));
		assertEquals(Rat(1, 3), evaluate(Div(Rat(2, 3), Rat(2, 1))));
		assertEquals(Rat(1, 2), evaluate(Div(Rat(2, 1), Rat(4, 1))));
	}

	@Test
	public void testNeg() {
		assertEquals(Rat(1, 2), evaluate(Neg(Neg(Neg(Neg(Rat(1, 2)))))));
		assertEquals(Rat(-1, 2), evaluate(Neg(Neg(Neg(Neg(Neg(Rat(1, 2))))))));
		assertEquals(Int(182), evaluate(Neg(Neg(Neg(Neg(Int(182)))))));
		assertEquals(Int(-182), evaluate(Neg(Neg(Neg(Neg(Neg(Int(182))))))));
	}

	@Test
	public void testSub() {
		assertEquals(Int(-1), evaluate(Sub(Int(7), Int(8))));
		assertEquals(Rat(1, 4), evaluate(Sub(Rat(3, 4), Rat(1, 2))));
		assertEquals(Rat(-1, 4), evaluate(Sub(Rat(3, 4), Rat(1, 1))));
	}

	@Test
	public void testAdd() {
		assertEquals(Int(6), evaluate(Add(Int(1), Int(2), Int(3))));
		assertEquals(Int(0), evaluate(Add(Int(1), Int(2), Int(-3))));
		assertEquals(Rat(7, 12), evaluate(Add(Rat(1, 3), Rat(1, 4))));
	}

	@Test
	public void testMul() {
		assertEquals(Int(30), evaluate(Mul(Int(2), Int(3), Int(5))));
		assertEquals(Rat(1, 1), evaluate(Mul(Rat(2, 1), Rat(1, 1), Rat(1, 2))));
		assertEquals(Rat(3, 4), evaluate(Mul(Rat(3, 2), Rat(1, 1), Rat(1, 2))));
	}

	@Test
	public void testIte() {
		assertEquals(Int(1), evaluate(Ite(True(), Int(1), Int(2))));
		assertEquals(Int(2), evaluate(Ite(False(), Int(1), Int(2))));
		assertEquals(Int(1), evaluate(Ite(True(), Ite(True(), Ite(True(), Int(1), Int(2)), Int(3)), Int(4))));
	}

	@Test
	public void testValuation() {
		final Valuation val = BasicValuation.builder().put(ca, Int(5)).put(cb, Int(10)).build();
		assertEquals(Int(15), evaluate(Add(a, b), val));
		assertEquals(Int(50), evaluate(Mul(a, b), val));
		assertEquals(Int(0), evaluate(Div(a, b), val));
	}

	@Test(expected = RuntimeException.class)
	public void testException() {
		evaluate(Add(a, Int(1)));
	}
}
