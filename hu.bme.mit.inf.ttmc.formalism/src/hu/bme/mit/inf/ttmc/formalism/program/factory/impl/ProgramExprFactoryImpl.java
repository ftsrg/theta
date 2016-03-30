package hu.bme.mit.inf.ttmc.formalism.program.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

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
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.PrimedExprImpl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.ProcCallExprImpl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.ProcRefExprImpl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.VarRefExprImpl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.ExprFactoryDecorator;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;
import hu.bme.mit.inf.ttmc.formalism.program.factory.ProgramExprFactory;

public class ProgramExprFactoryImpl extends ExprFactoryDecorator implements ProgramExprFactory {

	public ProgramExprFactoryImpl(final ExprFactory factory) {
		super(factory);
	}

	@Override
	public <T extends Type> VarRefExpr<T> Ref(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new VarRefExprImpl<>(varDecl);
	}

	@Override
	public <R extends Type> ProcRefExpr<R> Ref(final ProcDecl<R> procDecl) {
		checkNotNull(procDecl);
		return new ProcRefExprImpl<>(procDecl);
	}

	@Override
	public <R extends Type> ProcCallExpr<R> Call(final Expr<? extends ProcType<? extends R>> proc,
			final List<? extends Expr<?>> params) {
		checkNotNull(proc);
		checkNotNull(params);
		return new ProcCallExprImpl<>(proc, params);
	}

	@Override
	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op) {
		checkNotNull(op);
		return new PrimedExprImpl<>(op);
	}

}
