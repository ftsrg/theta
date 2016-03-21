package hu.bme.mit.inf.ttmc.formalism.common.factory;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public interface ProgramFactory extends VarDeclFactory {

	public <R extends Type> ProcDecl<R> Proc(final String name, List<? extends ParamDecl<? extends Type>> paramDecls,
			final R returnType);

	////

	public <R extends Type> ProcType<R> Proc(final List<? extends Type> paramTypes, final R returnType);

	////

	public <R extends Type> ProcRefExpr<R> Ref(final ProcDecl<R> procDecl);

	public <R extends Type> ProcCallExpr<R> Call(final Expr<? extends ProcType<? extends R>> proc,
			final List<? extends Expr<?>> params);

	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op);

}
