package hu.bme.mit.theta.frontend.aiger.impl.elements;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.List;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;

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
	public Expr<BoolType> getExpr(final List<HwElement> elements) {
		return varDecl.getRef();
	}

	public Expr<BoolType> getInitExpr() {
		return Not(varDecl.getRef());
	}

	public Expr<BoolType> getTransExpr(final List<HwElement> elements) {
		Expr<BoolType> expr = elements.get(nextState / 2).getExpr(elements);
		if (nextState % 2 != 0)
			expr = Not(expr);
		return Iff(Prime(varDecl.getRef()), expr);
	}

}
