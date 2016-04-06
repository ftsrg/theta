package hu.bme.mit.inf.ttmc.formalism.program.factory;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public interface ProgramExprFactory extends ExprFactory {

	public <T extends Type> VarRefExpr<T> Ref(final VarDecl<T> varDecl);

	public <R extends Type> ProcRefExpr<R> Ref(final ProcDecl<R> procDecl);

	public <R extends Type> ProcCallExpr<R> Call(final Expr<? extends ProcType<? extends R>> proc,
			final List<? extends Expr<?>> params);

	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op);

}
