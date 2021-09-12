package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.VarDecl;

public interface VarIndexing {
	VarIndexingBuilder transform();

	VarIndexing inc(VarDecl<?> varDecl, int n);

	VarIndexing inc(VarDecl<?> varDecl);

	VarIndexing add(VarIndexing indexing);

	VarIndexing sub(VarIndexing indexing);

	VarIndexing join(VarIndexing indexing);

	int get(VarDecl<?> varDecl);
}
