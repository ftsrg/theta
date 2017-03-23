package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.xta.XtaProcess;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc.Kind;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.CommitContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.StateDeclContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.UrgentContext;

final class XtaStateSymbol implements Symbol {

	private final String name;
	private final Kind kind;
	private final XtaExpression expression;

	public XtaStateSymbol(final XtaProcessSymbol scope, final StateDeclContext context, final UrgentContext urgent,
			final CommitContext commit) {
		checkNotNull(context);
		name = context.fId.getText();
		kind = isCommited(name, commit) ? Kind.COMMITTED : isUrgent(name, urgent) ? Kind.URGENT : Kind.NORMAL;
		expression = context.fExpression != null ? new XtaExpression(scope, context.fExpression) : null;
	}

	private static boolean isUrgent(final String name, final UrgentContext urgent) {
		if (urgent == null) {
			return false;
		} else {
			return urgent.fStateList.fIds.stream().anyMatch(id -> id.getText().equals(name));
		}

	}

	private static boolean isCommited(final String name, final CommitContext commit) {
		if (commit == null) {
			return false;
		} else {
			return commit.fStateList.fIds.stream().anyMatch(id -> id.getText().equals(name));
		}
	}

	@Override
	public String getName() {
		return name;
	}

	@SuppressWarnings("unchecked")
	public Loc instantiate(final XtaProcess process, final Environment env) {
		final Collection<Expr<BoolType>> invars;
		if (expression == null) {
			invars = Collections.emptySet();
		} else {
			final Expr<?> expr = expression.instantiate(env);
			final Expr<? extends BoolType> invar = ExprUtils.cast(expr, BoolType.class);
			final Collection<Expr<? extends BoolType>> conjuncts = ExprUtils.getConjuncts(invar);
			invars = conjuncts.stream().map(e -> (Expr<BoolType>) e).collect(toList());
		}

		final Loc loc = process.createLoc(process.getName() + "_" + name, kind, invars);
		return loc;
	}

}
