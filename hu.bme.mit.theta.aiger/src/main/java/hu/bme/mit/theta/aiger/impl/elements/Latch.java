package hu.bme.mit.theta.aiger.impl.elements;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.theta.formalism.common.expr.impl.Exprs2.Prime;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;

public final class Latch extends HWElement {
	private final int nextState;
	private final VarDecl<BoolType> varDecl;

	public Latch(final int nr, final String[] tokens) {
		this(nr, Integer.parseInt(tokens[0]), Integer.parseInt(tokens[1]));
	}

	public Latch(final int nr, final int actualState, final int nextState) {
		super(actualState / 2);
		this.nextState = nextState;
		varDecl = Var("L" + nr + "_l" + varId, Bool());
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HWElement> elements) {
		return varDecl.getRef();
	}

	public Expr<? extends BoolType> getInitExpr() {
		return Not(varDecl.getRef());
	}

	public Expr<? extends BoolType> getTransExpr(final List<HWElement> elements) {
		Expr<? extends BoolType> expr = elements.get(nextState / 2).getExpr(elements);
		if (nextState % 2 != 0)
			expr = Not(expr);
		return Iff(Prime(varDecl.getRef()), expr);
	}

}
