package hu.bme.mit.inf.ttmc.core.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.common.dsl.BasicScope;
import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.common.dsl.ScopedSymbol;
import hu.bme.mit.inf.ttmc.common.dsl.Symbol;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;

public abstract class ParametricSymbol implements ScopedSymbol {

	private final String name;
	private final List<ParamDecl<?>> paramDecls;

	private final Scope scope;

	public ParametricSymbol(final String name, final List<? extends ParamDecl<?>> paramDecls,
			final Scope enclosingScope) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkArgument(name.length() > 0);
		this.name = name;
		this.paramDecls = ImmutableList.copyOf(paramDecls);
		scope = new BasicScope(enclosingScope);

		declareParamDecls(paramDecls);
	}

	private void declareParamDecls(final List<? extends ParamDecl<?>> paramDecls) {
		paramDecls.forEach(p -> scope.declare(new DeclSymbol(p)));
	}

	public List<ParamDecl<?>> getParamDecls() {
		return paramDecls;
	}

	public List<DeclSymbol> getParamSymbols() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		return scope.resolve(name);
	}

	@Override
	public void declare(final Symbol symbol) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void declareAll(final Collection<? extends Symbol> symbols) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Optional<Scope> enclosingScope() {
		return scope.enclosingScope();
	}

	@Override
	public String getName() {
		return name;
	}

}
