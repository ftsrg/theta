package hu.bme.mit.inf.ttmc.aiger.impl.elements;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2;

public final class Latch extends HWElement {
	private final int nextState;
	private final VarDecl<BoolType> varDecl;

	public Latch(final int nr, final String[] tokens) {
		this(nr, Integer.parseInt(tokens[0]), Integer.parseInt(tokens[1]));
	}

	public Latch(final int nr, final int actualState, final int nextState) {
		super(actualState / 2);
		this.nextState = nextState;
		varDecl = Decls2.Var("L" + nr + "_l" + varId, Types.Bool());
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HWElement> elements) {
		return varDecl.getRef();
	}

	public Expr<? extends BoolType> getInitExpr() {
		return Exprs.Not(varDecl.getRef());
	}

	public Expr<? extends BoolType> getTransExpr(final List<HWElement> elements) {
		Expr<? extends BoolType> expr = elements.get(nextState / 2).getExpr(elements);
		if (nextState % 2 == 1)
			expr = Exprs.Not(expr);
		return Exprs.Iff(Exprs2.Prime(varDecl.getRef()), expr);
	}

}
