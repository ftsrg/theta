package hu.bme.mit.inf.ttmc.core.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.Decl;

public abstract class BasicScope implements Scope {

	final Optional<Scope> enclosingScope;
	final Map<String, Decl<?, ?>> stringToDecl;

	public BasicScope(final Scope eclosingScope) {
		this.enclosingScope = Optional.ofNullable(eclosingScope);
		stringToDecl = new HashMap<>();
	}

	@Override
	public Optional<Scope> getEnclosingScope() {
		return enclosingScope;
	}

	@Override
	public Optional<Decl<?, ?>> resolve(final String name) {
		checkNotNull(name);
		final Decl<?, ?> decl = stringToDecl.get(name);
		if (decl != null) {
			return Optional.of(decl);
		} else if (enclosingScope.isPresent()) {
			return enclosingScope.get().resolve(name);
		} else {
			return Optional.empty();
		}
	}

	@Override
	public void declare(final Decl<?, ?> decl) {
		checkNotNull(decl);
		checkArgument(!stringToDecl.containsKey(decl.getName()));
		stringToDecl.put(decl.getName(), decl);
	}

}
