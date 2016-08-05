package hu.bme.mit.inf.ttmc.core.dsl;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.Decl;

public interface Scope {

	public Optional<Decl<?, ?>> resolve(String name);

	public void declare(Decl<?, ?> decl);

	public Optional<Scope> getEnclosingScope();

}
