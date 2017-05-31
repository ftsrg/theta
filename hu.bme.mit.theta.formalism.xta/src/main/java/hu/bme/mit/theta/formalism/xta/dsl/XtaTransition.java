package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.emptyList;
import static java.util.Collections.emptySet;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.core.utils.impl.TypeUtils;
import hu.bme.mit.theta.formalism.xta.Label;
import hu.bme.mit.theta.formalism.xta.XtaProcess;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.IteratorDeclContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.SelectContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.TransitionContext;

final class XtaTransition implements Scope {
	private final XtaProcessSymbol scope;
	private final SymbolTable symbolTable;

	private final String sourceState;
	private final String targetState;
	private final List<XtaIteratorSymbol> selections;
	private final Optional<XtaExpression> guard;
	private final Optional<XtaSync> sync;
	private final List<XtaUpdate> updates;

	public XtaTransition(final XtaProcessSymbol scope, final TransitionContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);
		symbolTable = new SymbolTable();

		sourceState = context.fSourceId.getText();
		targetState = context.fTargetId.getText();

		selections = new ArrayList<>();
		guard = extractGuard(context);
		sync = extractSync(context);
		updates = extractUpdates(context);

		declareAllSelections(context.fTransitionBody.fSelect);
	}

	private Optional<XtaSync> extractSync(final TransitionContext context) {
		return Optional.ofNullable(context.fTransitionBody.fSync).map(s -> new XtaSync(this, s));
	}

	private Optional<XtaExpression> extractGuard(final TransitionContext context) {
		return Optional.ofNullable(context.fTransitionBody.fGuard).map(g -> new XtaExpression(this, g.fExpression));
	}

	private List<XtaUpdate> extractUpdates(final TransitionContext context) {
		if (context.fTransitionBody.fAssign != null) {
			if (context.fTransitionBody.fAssign.fExpressions != null) {
				return context.fTransitionBody.fAssign.fExpressions.stream().map(e -> new XtaUpdate(this, e))
						.collect(toList());
			}
		}
		return emptyList();
	}

	private void declareAllSelections(final SelectContext context) {
		if (context != null) {
			if (context.fIteratorDecls != null) {
				context.fIteratorDecls.forEach(this::declare);
			}
		}
	}

	private void declare(final IteratorDeclContext context) {
		final XtaIteratorSymbol iteratorSymbol = new XtaIteratorSymbol(this, context);
		selections.add(iteratorSymbol);
		symbolTable.add(iteratorSymbol);
	}

	////

	@SuppressWarnings("unchecked")
	public void instantiate(final XtaProcess process, final Environment env) {
		final XtaStateSymbol sourceSymbol = (XtaStateSymbol) resolve(sourceState).get();
		final XtaStateSymbol targetSymbol = (XtaStateSymbol) resolve(targetState).get();

		final Loc source = (Loc) env.eval(sourceSymbol);
		final Loc target = (Loc) env.eval(targetSymbol);

		final Collection<Expr<BoolType>> guards;
		if (guard.isPresent()) {
			final Expr<?> expr = guard.get().instantiate(env);
			final Expr<? extends BoolType> guardExpr = TypeUtils.cast(expr, BoolType.class);
			final Collection<Expr<? extends BoolType>> conjuncts = ExprUtils.getConjuncts(guardExpr);
			guards = conjuncts.stream().map(e -> (Expr<BoolType>) e).collect(toList());
		} else {
			guards = emptySet();
		}

		final List<Stmt> assignments = updates.stream().map(u -> u.instantiate(env)).collect(toList());
		final Optional<Label> label = sync.map(s -> s.instantiate(env));

		process.createEdge(source, target, guards, label, assignments);
	}

	////

	@Override
	public Optional<? extends Scope> enclosingScope() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		final Optional<Symbol> symbol = symbolTable.get(name);
		if (symbol.isPresent()) {
			return symbol;
		} else {
			return scope.resolve(name);
		}
	}

}