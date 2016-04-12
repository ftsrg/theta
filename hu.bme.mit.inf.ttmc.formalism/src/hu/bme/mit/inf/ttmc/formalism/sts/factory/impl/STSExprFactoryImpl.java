package hu.bme.mit.inf.ttmc.formalism.sts.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.PrimedExprImpl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.ExprFactoryDecorator;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;

public class STSExprFactoryImpl extends ExprFactoryDecorator implements STSExprFactory {

	public STSExprFactoryImpl(final ExprFactory factory) {
		super(factory);
	}

	@Override
	public <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op) {
		checkNotNull(op);
		return new PrimedExprImpl<>(op);
	}

}
