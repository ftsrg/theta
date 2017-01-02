package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.createConstDecl;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.createVarDecl;

import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.ScopedSymbol;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.NestedAssignment;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ConstDeclContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaDeclContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaSpecContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.VarDeclContext;

final class TcfaSpecSymbol implements ScopedSymbol {

	private final TcfaSpecContext tcfaSpecContext;

	private final SymbolTable symbolTable;

	private final String name;
	private final List<TcfaParamDecl<?>> params;

	private TcfaSpecSymbol(final TcfaSpecContext tcfaSpecContext) {
		this.tcfaSpecContext = checkNotNull(tcfaSpecContext);
		symbolTable = new SymbolTable();
		name = tcfaSpecContext.name.getText();
		params = TcfaDslHelper.createTcfaParamList(tcfaSpecContext.tcfaParamDecls);

		declareParams();
		declareConsts();
		declareVars();
		declareTcfas();
	}

	public static TcfaSpecSymbol create(final TcfaSpecContext tcfaSpecContext) {
		return new TcfaSpecSymbol(tcfaSpecContext);
	}

	////

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Optional<Scope> enclosingScope() {
		return Optional.empty();
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		return symbolTable.get(name);
	}

	////

	public TcfaSpec instantiate(final List<? extends Expr<?>> args) {
		final List<Expr<?>> simplifiedArgs = ExprUtils.simplifyAll(args);
		final TcfaParamBinding binding = TcfaParamBinding.create(params, simplifiedArgs);
		// TODO Handle recursive constant definitions
		final Assignment constAssignment = TcfaDslHelper.createConstDefs(this, binding, tcfaSpecContext.constDecls);
		final Assignment assignment = NestedAssignment.create(binding, constAssignment);
		final TcfaSpec tcfaSpec = TcfaSpec.create(this, assignment);
		return tcfaSpec;
	}

	////

	private void declareParams() {
		params.forEach(this::declareParam);
	}

	private void declareParam(final TcfaParamDecl<?> paramDecl) {
		final Symbol symbol = DeclSymbol.of(paramDecl);
		symbolTable.add(symbol);
	}

	private void declareConsts() {
		tcfaSpecContext.constDecls.forEach(this::declareConst);
	}

	private void declareConst(final ConstDeclContext constDeclContext) {
		final ConstDecl<?> constDecl = createConstDecl(constDeclContext);
		final Symbol symbol = DeclSymbol.of(constDecl);
		symbolTable.add(symbol);
	}

	private void declareVars() {
		tcfaSpecContext.varDecls.forEach(this::declareVar);
	}

	private void declareVar(final VarDeclContext varDeclContext) {
		final VarDecl<?> varDecl = createVarDecl(varDeclContext);
		final Symbol symbol = DeclSymbol.of(varDecl);
		symbolTable.add(symbol);
	}

	private void declareTcfas() {
		tcfaSpecContext.tcfaDecls.forEach(this::declareTcfa);
	}

	private void declareTcfa(final TcfaDeclContext tcfaDeclContext) {
		final TcfaDeclSymbol symbol = TcfaDeclSymbol.create(this, tcfaDeclContext);
		symbolTable.add(symbol);
	}

}
