package hu.bme.mit.inf.ttmc.core.dsl;

import static com.google.common.base.Preconditions.checkState;

public class ScopeStack {

	private Scope currentScope;

	public ScopeStack(final Scope scope) {
		currentScope = scope;
	}

	public void pop() {
		checkState(currentScope.getEnclosingScope().isPresent());
		currentScope = currentScope.getEnclosingScope().get();
	}

	public void push() {
		currentScope = new LocalScope(currentScope);
	}

	public Scope currentScope() {
		return currentScope;
	}

}
