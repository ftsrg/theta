package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.ScopedSymbol;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.NestedAssignment;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaDeclContext;

final class TcfaDeclSymbol implements ScopedSymbol {

	private final TcfaDeclContext tcfaDeclContext;

	private final TcfaSpecSymbol enclosingScope;
	private final SymbolTable symbolTable;

	private final String name;
	private final List<TcfaParamDecl<?>> params;

	private TcfaDeclSymbol(final TcfaSpecSymbol enclosingScope, final TcfaDeclContext tcfaDeclContext) {
		this.enclosingScope = checkNotNull(enclosingScope);
		this.tcfaDeclContext = checkNotNull(tcfaDeclContext);
		symbolTable = new SymbolTable();
		name = tcfaDeclContext.name.getText();
		params = TcfaDslHelper.createTcfaParamList(tcfaDeclContext.tcfaParamDecls);

		declareParams();
	}

	public static TcfaDeclSymbol create(final TcfaSpecSymbol enclosingScope, final TcfaDeclContext tcfaDeclCtx) {
		return new TcfaDeclSymbol(enclosingScope, tcfaDeclCtx);
	}

	////

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Optional<TcfaSpecSymbol> enclosingScope() {
		return Optional.of(enclosingScope);
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		final Optional<Symbol> optSymbol = symbolTable.get(name);
		if (optSymbol.isPresent()) {
			return optSymbol;
		} else {
			return enclosingScope.resolve(name);
		}
	}

	////

	public TCFA instantiate(final Assignment assignment, final List<? extends Expr<?>> args) {
		final List<Expr<?>> simplifiedArgs = ExprUtils.simplifyAll(args);
		final TcfaParamBinding binding = TcfaParamBinding.create(params, simplifiedArgs);
		final Assignment newAssignment = NestedAssignment.create(assignment, binding);
		final TCFA tcfa = TcfaCreator.createTcfa(this, newAssignment, tcfaDeclContext.def);
		return tcfa;
	}

	////

	// TODO Eliminate copy-paste code

	private void declareParams() {
		params.forEach(this::declareParam);
	}

	private void declareParam(final TcfaParamDecl<?> paramDecl) {
		final Symbol symbol = DeclSymbol.of(paramDecl);
		symbolTable.add(symbol);
	}
}
