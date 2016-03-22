package hu.bme.mit.inf.ttmc.formalism.sts.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.PrimedExprImpl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.VarRefExprImpl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.ExprFactoryDecorator;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;

public class STSExprFactoryImpl extends ExprFactoryDecorator implements STSExprFactory {

	public STSExprFactoryImpl(final ExprFactory factory) {
		super(factory);
	}

	@Override
	public <T extends Type> VarRefExpr<T> Ref(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new VarRefExprImpl<>(varDecl);
	}

	@Override
	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op) {
		checkNotNull(op);
		return new PrimedExprImpl<>(op);
	}

}
