package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.xta.ChanType;
import hu.bme.mit.theta.formalism.xta.SyncLabel;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.SyncContext;

final class XtaSync {

	private final XtaExpression expression;
	private final SyncKind syncKind;

	public XtaSync(final XtaTransition scope, final SyncContext context) {
		checkNotNull(context);
		expression = new XtaExpression(scope, context.fExpression);
		syncKind = context.fReceive != null ? SyncKind.RECEIVE : SyncKind.EMIT;
	}

	public static enum SyncKind {
		EMIT, RECEIVE
	}

	public SyncLabel instantiate(final Environment env) {
		final Expr<?> expr = expression.instantiate(env);
		final Expr<? extends ChanType> castExpr = ExprUtils.cast(expr, ChanType.class);
		@SuppressWarnings("unchecked")
		final Expr<ChanType> chanExpr = (Expr<ChanType>) castExpr;
		if (syncKind == SyncKind.EMIT) {
			return SyncLabel.emit(chanExpr);
		} else if (syncKind == SyncKind.RECEIVE) {
			return SyncLabel.receive(chanExpr);
		} else {
			throw new AssertionError();
		}
	}

}
