package hu.bme.mit.theta.core.utils.indexings;

import hu.bme.mit.theta.core.decl.VarDecl;

public interface VarIndexingBuilder {
	VarIndexingBuilder inc(VarDecl<?> varDecl);

	VarIndexingBuilder incAll();

	VarIndexingBuilder add(VarIndexingBuilder that);

	VarIndexingBuilder sub(VarIndexingBuilder that);

	VarIndexingBuilder join(VarIndexingBuilder that);

	int get(VarDecl<?> varDecl);

	VarIndexing build();
}
