package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.dsl.Environment;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.ProcDeclContext;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.SpecContext;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.VarDeclContext;

final class CfaSpecification implements Scope {

	private final SymbolTable symbolTable;

	private final List<CfaVariableSymbol> variables;
	private final List<CfaProcessSymbol> processes;

	private CfaSpecification(final SpecContext context) {
		checkNotNull(context);
		symbolTable = new SymbolTable();

		variables = createVariables(context.varDecls);
		processes = createProcesses(context.procDecls);

		declareAll(variables);
		declareAll(processes);
	}

	public static CfaSpecification fromContext(final SpecContext context) {
		return new CfaSpecification(context);
	}

	////

	public CFA instantiate() {
		final Environment env = new Environment();

		for (final CfaVariableSymbol variable : variables) {
			final VarDecl<?> var = variable.instantiate();
			env.define(variable, var);
		}

		final List<CfaProcessSymbol> mainProcesses = processes.stream().filter(CfaProcessSymbol::isMain)
				.collect(toList());

		if (mainProcesses.size() < 1) {
			throw new IllegalArgumentException("No main process defined");
		} else if (mainProcesses.size() > 1) {
			throw new IllegalArgumentException("More than one main process is defined");
		} else {
			final CfaProcessSymbol process = Utils.singleElementOf(mainProcesses);
			final CFA cfa = process.instantiate(env);
			return cfa;
		}
	}

	////

	@Override
	public Optional<Scope> enclosingScope() {
		return Optional.empty();
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		return symbolTable.get(name);
	}

	////

	private void declareAll(final Iterable<? extends Symbol> symbols) {
		symbolTable.addAll(symbols);
	}

	private List<CfaVariableSymbol> createVariables(final List<VarDeclContext> varDeclContexts) {
		final List<CfaVariableSymbol> result = new ArrayList<>();
		for (final VarDeclContext varDeclContext : varDeclContexts) {
			final CfaVariableSymbol symbol = new CfaVariableSymbol(varDeclContext);
			result.add(symbol);
		}
		return result;
	}

	private List<CfaProcessSymbol> createProcesses(final List<ProcDeclContext> procDeclContexts) {
		final List<CfaProcessSymbol> result = new ArrayList<>();
		for (final ProcDeclContext procDeclContext : procDeclContexts) {
			final CfaProcessSymbol symbol = new CfaProcessSymbol(this, procDeclContext);
			result.add(symbol);
		}
		return result;
	}

}
