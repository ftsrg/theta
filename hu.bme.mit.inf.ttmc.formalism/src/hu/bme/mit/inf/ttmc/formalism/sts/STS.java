package hu.bme.mit.inf.ttmc.formalism.sts;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

/**
 * Symbolic Transition System (STS) interface.
 */
public interface STS {

	public Collection<VarDecl<? extends Type>> getVars();

	public Collection<Expr<? extends BoolType>> getInit();

	public Collection<Expr<? extends BoolType>> getInvar();

	public Collection<Expr<? extends BoolType>> getTrans();

	public Expr<? extends BoolType> getProp();

	// Unrolling methods

	public Expr<? extends BoolType> unroll(final Expr<? extends BoolType> expr, final int i);

	public Collection<Expr<? extends BoolType>> unrollInit(final int i);

	public Collection<Expr<? extends BoolType>> unrollTrans(final int i);

	public Collection<Expr<? extends BoolType>> unrollInv(final int i);

	public Expr<? extends BoolType> unrollProp(final int i);

	public AndExpr getConcreteState(final Model model, final int i);

	public AndExpr getConcreteState(final Model model, final int i, final Collection<VarDecl<? extends Type>> variables);

	public List<AndExpr> extractTrace(final Model model, final int length);

	public List<AndExpr> extractTrace(final Model model, final int length, final Collection<VarDecl<? extends Type>> variables);

	public Expr<? extends BoolType> foldin(final Expr<? extends BoolType> expr, final int i);
}
