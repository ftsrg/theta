package hu.bme.mit.inf.ttmc.analysis.tests;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.pred.precisions.TreePredPrecision;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2;

public class TreePrecisionTests {

	@Test
	public void test() {
		final List<Expr<? extends BoolType>> preds = new ArrayList<>();
		final VarDecl<IntType> x = Decls2.Var("x", Types.Int());
		final VarDecl<IntType> y = Decls2.Var("y", Types.Int());

		final Valuation.Builder valBuilder = new Valuation.Builder();
		valBuilder.put(x, Exprs.Int(2));
		valBuilder.put(y, Exprs.Int(2));
		final Valuation valuation = valBuilder.build();

		preds.add(Exprs.Eq(x.getRef(), Exprs.Int(2)));
		preds.add(Exprs.Lt(y.getRef(), Exprs.Int(2)));
		preds.add(Exprs.Eq(y.getRef(), x.getRef()));

		final TreePredPrecision precision = TreePredPrecision.create(preds);
		final PredState as = precision.mapToAbstractState(valuation);
		System.out.println(as);
		precision.refine(as, Exprs.Gt(x.getRef(), Exprs.Int(2)));
		System.out.println(precision.mapToAbstractState(valuation));

	}
}
