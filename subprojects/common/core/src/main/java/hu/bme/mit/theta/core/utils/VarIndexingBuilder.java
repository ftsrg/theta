package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.VarDecl;

public abstract class VarIndexingBuilder {
	protected int defaultIndex;

	public abstract VarIndexingBuilder inc(VarDecl<?> varDecl, int n);

	public abstract VarIndexingBuilder inc(VarDecl<?> varDecl);

	public abstract VarIndexingBuilder incAll();

	public abstract VarIndexingBuilder add(VarIndexingBuilder that);

	public abstract VarIndexingBuilder sub(VarIndexingBuilder that);

	public abstract VarIndexingBuilder join(VarIndexingBuilder that);

	public abstract int get(VarDecl<?> varDecl);

	public abstract VarIndexing build();
}
