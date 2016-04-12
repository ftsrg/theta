package hu.bme.mit.inf.ttmc.solver.z3.tests;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Param;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.App;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Forall;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Mul;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Ref;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Func;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;

import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.core.SolverManager;
import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.core.solver.Interpolant;
import hu.bme.mit.inf.ttmc.core.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.core.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.core.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.FuncType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class Z3ItpSolverTests {

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
		final SolverManager manager = new Z3SolverManager();
		final SolverFactory sf = manager.getSolverFactory();

		solver = sf.createItpSolver();

		final ConstDecl<IntType> ad = Const("a", Int());
		final ConstDecl<IntType> bd = Const("b", Int());
		final ConstDecl<IntType> cd = Const("c", Int());
		final ConstDecl<IntType> dd = Const("d", Int());
		final ConstDecl<IntType> ed = Const("e", Int());
		final ConstDecl<FuncType<IntType, IntType>> fd = Const("f", Func(Int(), Int()));
		final ConstDecl<FuncType<IntType, IntType>> gd = Const("g", Func(Int(), Int()));

		a = Ref(ad);
		b = Ref(bd);
		c = Ref(cd);
		d = Ref(dd);
		e = Ref(ed);
		f = Ref(fd);
		g = Ref(gd);
	}

	@Test
	public void testBinaryInterpolation() {
		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		solver.add(A, Eq(a, b));
		solver.add(A, Eq(a, c));
		solver.add(B, Eq(b, d));
		solver.add(B, Neq(c, d));

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

		solver.add(I1, Eq(a, b));
		solver.add(I1, Eq(a, c));
		solver.add(I2, Eq(c, d));
		solver.add(I3, Eq(b, e));
		solver.add(I3, Neq(d, e));

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

		solver.add(I1, Eq(a, Int(0)));
		solver.add(I1, Eq(a, b));
		solver.add(I2, Eq(c, d));
		solver.add(I2, Eq(d, Int(1)));
		solver.add(I3, Eq(b, c));

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

		solver.add(A, Eq(App(f, a), c));
		solver.add(A, Eq(App(f, b), d));
		solver.add(B, Eq(a, b));
		solver.add(B, Neq(App(g, c), App(g, d)));

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

		solver.add(A, Eq(b, Mul(ImmutableList.of(Int(2), a))));
		solver.add(B, Eq(b, Add(ImmutableList.of(Mul(ImmutableList.of(Int(2), c)), Int(1)))));

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

		final ConstDecl<IntType> id = Const("i", Int());
		final ConstDecl<FuncType<IntType, BoolType>> pd = Const("p", Func(Int(), Bool()));
		final ConstDecl<FuncType<IntType, BoolType>> qd = Const("q", Func(Int(), Bool()));
		final ParamDecl<IntType> x1d = Param("x", Int());
		final ParamDecl<IntType> x2d = Param("x", Int());

		final Expr<IntType> i = Ref(id);
		final Expr<FuncType<IntType, BoolType>> p = Ref(pd);
		final Expr<FuncType<IntType, BoolType>> q = Ref(qd);
		final Expr<IntType> x1 = Ref(x1d);
		final Expr<IntType> x2 = Ref(x2d);

		solver.add(A, Forall(ImmutableList.of(x1d), Imply(App(q, x1), App(p, x1))));
		solver.add(A, Forall(ImmutableList.of(x2d), Not(App(p, x2))));
		solver.add(B, App(q, i));

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

		solver.add(A, Eq(a, b));
		solver.add(B, Eq(b, c));

		solver.push();

		solver.add(A, Neq(a, c));
		solver.check();

		solver.pop();

		solver.add(B, Neq(a, c));
		solver.check();
		final Interpolant itp = solver.getInterpolant(pattern);

		System.out.println(itp.eval(A));
		System.out.println("----------");
	}

}
