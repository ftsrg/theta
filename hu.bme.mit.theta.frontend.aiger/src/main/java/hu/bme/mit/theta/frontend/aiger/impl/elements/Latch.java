package hu.bme.mit.theta.frontend.aiger.impl.elements;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;

import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public final class Latch extends HwElement {
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
	public Expr<? extends BoolType> getExpr(final List<HwElement> elements) {
		return varDecl.getRef();
	}

	public Expr<? extends BoolType> getInitExpr() {
		return Not(varDecl.getRef());
	}

	public Expr<? extends BoolType> getTransExpr(final List<HwElement> elements) {
		Expr<? extends BoolType> expr = elements.get(nextState / 2).getExpr(elements);
		if (nextState % 2 != 0)
			expr = Not(expr);
		return Iff(Prime(varDecl.getRef()), expr);
	}

}
