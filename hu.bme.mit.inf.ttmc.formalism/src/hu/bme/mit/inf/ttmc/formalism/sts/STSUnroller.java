package hu.bme.mit.inf.ttmc.formalism.sts;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public interface STSUnroller {
	public Expr<? extends BoolType> unroll(final Expr<? extends BoolType> expr, final int i);

	public Collection<Expr<? extends BoolType>> init(final int i);

	public Collection<Expr<? extends BoolType>> trans(final int i);

	public Collection<Expr<? extends BoolType>> inv(final int i);

	public Expr<? extends BoolType> prop(final int i);

	public AndExpr getConcreteState(final Model model, final int i);

	public AndExpr getConcreteState(final Model model, final int i,
			final Collection<VarDecl<? extends Type>> variables);

	public List<AndExpr> extractTrace(final Model model, final int length);

	public List<AndExpr> extractTrace(final Model model, final int length,
			final Collection<VarDecl<? extends Type>> variables);

	public Expr<? extends BoolType> foldin(final Expr<? extends BoolType> expr, final int i);
}
