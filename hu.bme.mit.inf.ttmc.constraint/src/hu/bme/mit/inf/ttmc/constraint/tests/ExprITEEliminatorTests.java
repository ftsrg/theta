package hu.bme.mit.inf.ttmc.constraint.tests;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprITEEliminator;

public class ExprITEEliminatorTests {
	// Manager and factories
	private ConstraintManager manager;
	private ExprFactory efc;
	private DeclFactory dfc;
	private TypeFactory tfc;
	// Constants for testing
	private ConstRefExpr<BoolType> cA, cB, cC, cD, cE;
	private ConstRefExpr<IntType> cX, cY, cZ, cT;
	private IntLitExpr i1, i2, i3, i4, i5;
	// Transformator
	ExprITEEliminator eliminator;
	
	@Before
	public void before(){
		// Create manager and get factories
		manager = new ConstraintManagerImpl();
		efc = manager.getExprFactory();
		dfc = manager.getDeclFactory();
		tfc = manager.getTypeFactory();
		// Create constants
		cA = efc.Ref(dfc.Const("A", tfc.Bool()));
		cB = efc.Ref(dfc.Const("B", tfc.Bool()));
		cC = efc.Ref(dfc.Const("C", tfc.Bool()));
		cD = efc.Ref(dfc.Const("D", tfc.Bool()));
		cE = efc.Ref(dfc.Const("E", tfc.Bool()));
		cX = efc.Ref(dfc.Const("X", tfc.Int()));
		cY = efc.Ref(dfc.Const("Y", tfc.Int()));
		cZ = efc.Ref(dfc.Const("Z", tfc.Int()));
		cT = efc.Ref(dfc.Const("T", tfc.Int()));
		i1 = efc.Int(1);
		i2 = efc.Int(2);
		i3 = efc.Int(3);
		i4 = efc.Int(4);
		i5 = efc.Int(5);
		// Create transformator
		eliminator = new ExprITEEliminator(manager);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testSimple() {
		// if A then B else C
		Assert.assertEquals(
			eliminator.eliminate(efc.Ite(cA, cB, cC)),
			efc.And(efc.Or(efc.Not(cA), cB), efc.Or(cA, cC))
			);
		
		// if A then (if B then C else D) else E
		Assert.assertEquals(
			eliminator.eliminate(efc.Ite(cA, efc.Ite(cB, cC, cD), cE)),
			efc.And(
					efc.Or(efc.Not(cA), efc.And(
							efc.Or(efc.Not(cB), cC),
							efc.Or(cB, cD))),
					efc.Or(cA, cE))
			);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testUnary() {
		// !(if A then B else C)
		Assert.assertEquals(
				eliminator.eliminate(efc.Not(efc.Ite(cA, cB, cC))),
				efc.Not(efc.And(efc.Or(efc.Not(cA), cB), efc.Or(cA, cC)))
				);
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testBinary() {
		// A -> (if B then C else D)
		Assert.assertEquals(
				eliminator.eliminate(efc.Imply(cA, efc.Ite(cB, cC, cD))),
				efc.Imply(cA, efc.And(efc.Or(efc.Not(cB), cC), efc.Or(cB, cD)))
				);
		// (if B then C else D) -> A
		Assert.assertEquals(
				eliminator.eliminate(efc.Imply(efc.Ite(cB, cC, cD), cA)),
				efc.Imply(efc.And(efc.Or(efc.Not(cB), cC), efc.Or(cB, cD)), cA)
				);
		// X = (if A then Y else Z)
		Assert.assertEquals(
				eliminator.eliminate(efc.Eq(cX, efc.Ite(cA, cY, cZ))),
				efc.And(efc.Or(efc.Not(cA), efc.Eq(cX, cY)), efc.Or(cA, efc.Eq(cX, cZ)))
				);
		// (if A then Y else Z) = X
		Assert.assertEquals(
				eliminator.eliminate(efc.Eq(efc.Ite(cA, cY, cZ), cX)),
				efc.And(efc.Or(efc.Not(cA), efc.Eq(cY, cX)), efc.Or(cA, efc.Eq(cZ, cX)))
				);
		// X = (if A then (if B then Y else Z) else T)
		Assert.assertEquals(
				eliminator.eliminate(efc.Eq(cX, efc.Ite(cA, efc.Ite(cB, cY, cZ), cT))),
				efc.And(
						efc.Or(efc.Not(cA), efc.And(
								efc.Or(efc.Not(cB), efc.Eq(cX, cY)),
								efc.Or(cB, efc.Eq(cX, cZ)))),
						efc.Or(cA, efc.Eq(cX, cT)))
				);
		// (if A then (if B then Y else Z) else T) = X
		Assert.assertEquals(
				eliminator.eliminate(efc.Eq(efc.Ite(cA, efc.Ite(cB, cY, cZ), cT), cX)),
				efc.And(
						efc.Or(efc.Not(cA), efc.And(
								efc.Or(efc.Not(cB), efc.Eq(cY, cX)),
								efc.Or(cB, efc.Eq(cZ, cX)))),
						efc.Or(cA, efc.Eq(cT, cX)))
				);
		// (if A then X else Y) = (if B then Z else T)
		Assert.assertEquals(
			eliminator.eliminate(efc.Eq(efc.Ite(cA, cX, cY), efc.Ite(cB, cZ, cT))),
			efc.And(
					efc.Or(efc.Not(cA), efc.And(
							efc.Or(efc.Not(cB), efc.Eq(cX, cZ)),
							efc.Or(cB, efc.Eq(cX, cT)))),
					efc.Or(cA, efc.And(
							efc.Or(efc.Not(cB), efc.Eq(cY, cZ)),
							efc.Or(cB, efc.Eq(cY, cT))))));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testMultiary() {
		// A or B or (if C then D else E)
		Assert.assertEquals(
				eliminator.eliminate(efc.Or(cA, cB, efc.Ite(cC, cD, cE))),
				efc.Or(cA, cB, efc.And(efc.Or(efc.Not(cC), cD), efc.Or(cC, cE)))
				);
		// 1 = 2 + (if A then 3 else 4) + 5
		Assert.assertEquals(
				eliminator.eliminate(efc.Eq(i1, efc.Add(i2, efc.Ite(cA, i3, i4), i5))),
				efc.And(
						efc.Or(efc.Not(cA), efc.Eq(i1, efc.Add(i2, i3, i5))),
						efc.Or(cA, efc.Eq(i1, efc.Add(i2, i4, i5)))));
		// 1 = 2 + (if A then 3 else 4) + (if B then X else Y)
				Assert.assertEquals(
						eliminator.eliminate(efc.Eq(i1, efc.Add(i2, efc.Ite(cA, i3, i4), efc.Ite(cB, cX, cY)))),
						efc.And(
								efc.Or(efc.Not(cA), efc.And(
										efc.Or(efc.Not(cB), efc.Eq(i1, efc.Add(i2, i3, cX))),
										efc.Or(cB,efc.Eq(i1, efc.Add(i2, i3, cY))))),
								efc.Or(cA, efc.And(
										efc.Or(efc.Not(cB),efc.Eq(i1, efc.Add(i2, i4, cX))),
										efc.Or(cB,efc.Eq(i1, efc.Add(i2, i4, cY)))))));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testNothingHappening() {
		List<Expr<? extends BoolType>> expressions = new ArrayList<>();
		expressions.add(efc.And(cA, cB, cD));
		expressions.add(efc.Eq(cX, efc.Neg(cY)));
		expressions.add(efc.Geq(efc.Sub(cX, cY), efc.Add(cX, cZ, cT)));

		for (Expr<? extends BoolType> expr : expressions) Assert.assertEquals(expr, eliminator.eliminate(expr));
	}
}
