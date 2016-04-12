package hu.bme.mit.inf.ttmc.constraint.z3.tests;

import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.core.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.core.solver.Interpolant;
import hu.bme.mit.inf.ttmc.core.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.core.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.core.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.FuncType;
import hu.bme.mit.inf.ttmc.core.type.IntType;

public class Z3ItpSolverTests {

	TypeFactory tf;
	DeclFactory df;
	ExprFactory ef;

	ItpSolver solver;

	Expr<IntType> a;
	Expr<IntType> b;
	Expr<IntType> c;
	Expr<IntType> d;
	Expr<IntType> e;
	Expr<FuncType<IntType, IntType>> f;
	Expr<FuncType<IntType, IntType>> g;

	@Before
	public void initialize() {
		final ConstraintManager manager = new Z3ConstraintManager();
		final SolverFactory sf = manager.getSolverFactory();

		tf = manager.getTypeFactory();
		df = manager.getDeclFactory();
		ef = manager.getExprFactory();
		solver = sf.createItpSolver();

		final ConstDecl<IntType> ad = df.Const("a", tf.Int());
		final ConstDecl<IntType> bd = df.Const("b", tf.Int());
		final ConstDecl<IntType> cd = df.Const("c", tf.Int());
		final ConstDecl<IntType> dd = df.Const("d", tf.Int());
		final ConstDecl<IntType> ed = df.Const("e", tf.Int());
		final ConstDecl<FuncType<IntType, IntType>> fd = df.Const("f", tf.Func(tf.Int(), tf.Int()));
		final ConstDecl<FuncType<IntType, IntType>> gd = df.Const("g", tf.Func(tf.Int(), tf.Int()));

		a = ef.Ref(ad);
		b = ef.Ref(bd);
		c = ef.Ref(cd);
		d = ef.Ref(dd);
		e = ef.Ref(ed);
		f = ef.Ref(fd);
		g = ef.Ref(gd);
	}

	@Test
	public void testBinaryInterpolation() {
		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		solver.add(A, ef.Eq(a, b));
		solver.add(A, ef.Eq(a, c));
		solver.add(B, ef.Eq(b, d));
		solver.add(B, ef.Neq(c, d));

		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(A));
		System.out.println("----------");
	}

	@Test
	public void testSequenceInterpolation() {
		final ItpMarker I1 = solver.createMarker();
		final ItpMarker I2 = solver.createMarker();
		final ItpMarker I3 = solver.createMarker();
		final ItpPattern pattern = solver.createSeqPattern(ImmutableList.of(I1, I2, I3));

		solver.add(I1, ef.Eq(a, b));
		solver.add(I1, ef.Eq(a, c));
		solver.add(I2, ef.Eq(c, d));
		solver.add(I3, ef.Eq(b, e));
		solver.add(I3, ef.Neq(d, e));

		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(I1));
		System.out.println(itp.eval(I2));
		System.out.println("----------");
	}

	@Test
	public void testTreeInterpolation() {
		final ItpMarker I1 = solver.createMarker();
		final ItpMarker I2 = solver.createMarker();
		final ItpMarker I3 = solver.createMarker();
		final ItpPattern pattern = solver.createPattern(I3);
		pattern.createChild(I1);
		pattern.createChild(I2);

		solver.add(I1, ef.Eq(a, ef.Int(0)));
		solver.add(I1, ef.Eq(a, b));
		solver.add(I2, ef.Eq(c, d));
		solver.add(I2, ef.Eq(d, ef.Int(1)));
		solver.add(I3, ef.Eq(b, c));

		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(I1));
		System.out.println(itp.eval(I2));
		System.out.println("----------");
	}

	@Test
	public void testEUF() {
		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		solver.add(A, ef.Eq(ef.App(f, a), c));
		solver.add(A, ef.Eq(ef.App(f, b), d));
		solver.add(B, ef.Eq(a, b));
		solver.add(B, ef.Neq(ef.App(g, c), ef.App(g, d)));

		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(A));
		System.out.println("----------");
	}

	@Test
	public void testLIA() {
		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		solver.add(A, ef.Eq(b, ef.Mul(ImmutableList.of(ef.Int(2), a))));
		solver.add(B, ef.Eq(b, ef.Add(ImmutableList.of(ef.Mul(ImmutableList.of(ef.Int(2), c)), ef.Int(1)))));

		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(A));
		System.out.println("----------");
	}

	@Test
	public void testQuantifiers() {
		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		final ConstDecl<IntType> id = df.Const("i", tf.Int());
		final ConstDecl<FuncType<IntType, BoolType>> pd = df.Const("p", tf.Func(tf.Int(), tf.Bool()));
		final ConstDecl<FuncType<IntType, BoolType>> qd = df.Const("q", tf.Func(tf.Int(), tf.Bool()));
		final ParamDecl<IntType> x1d = df.Param("x", tf.Int());
		final ParamDecl<IntType> x2d = df.Param("x", tf.Int());

		final Expr<IntType> i = ef.Ref(id);
		final Expr<FuncType<IntType, BoolType>> p = ef.Ref(pd);
		final Expr<FuncType<IntType, BoolType>> q = ef.Ref(qd);
		final Expr<IntType> x1 = ef.Ref(x1d);
		final Expr<IntType> x2 = ef.Ref(x2d);

		solver.add(A, ef.Forall(ImmutableList.of(x1d), ef.Imply(ef.App(q, x1), ef.App(p, x1))));
		solver.add(A, ef.Forall(ImmutableList.of(x2d), ef.Not(ef.App(p, x2))));
		solver.add(B, ef.App(q, i));

		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(A));
		System.out.println("----------");
	}

	@Test
	public void testPushPop() {
		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		solver.add(A, ef.Eq(a, b));
		solver.add(B, ef.Eq(b, c));

		solver.push();

		solver.add(A, ef.Neq(a, c));
		solver.check();

		solver.pop();

		solver.add(B, ef.Neq(a, c));
		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(A));
		System.out.println("----------");
	}

}
