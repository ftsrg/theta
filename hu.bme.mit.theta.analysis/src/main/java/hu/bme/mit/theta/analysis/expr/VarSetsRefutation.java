package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.Iterator;
import java.util.List;
import java.util.Set;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public final class VarSetsRefutation implements Refutation, Iterable<Set<VarDecl<? extends Type>>> {

	private final List<Set<VarDecl<? extends Type>>> varSets;
	private final int pruneIndex;

	private VarSetsRefutation(final List<Set<VarDecl<? extends Type>>> varSets) {
		checkNotNull(varSets);
		checkArgument(!varSets.isEmpty());
		this.varSets = ImmutableList.copyOf(varSets);
		int i = 0;
		while (i < varSets.size() && varSets.get(i).isEmpty()) {
			++i;
		}
		this.pruneIndex = i;
		checkState(0 <= this.pruneIndex && this.pruneIndex < varSets.size());
	}

	public static VarSetsRefutation create(final List<Set<VarDecl<? extends Type>>> varSets) {
		return new VarSetsRefutation(varSets);
	}

	public List<Set<VarDecl<? extends Type>>> getVarSets() {
		return varSets;
	}

	@Override
	public Iterator<Set<VarDecl<? extends Type>>> iterator() {
		return varSets.iterator();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(varSets).toString();
	}

	@Override
	public int getPruneIndex() {
		return pruneIndex;
	}
}
