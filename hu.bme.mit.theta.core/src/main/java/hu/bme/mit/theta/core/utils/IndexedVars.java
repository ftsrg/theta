package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.StringJoiner;
import java.util.stream.Collectors;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.ToStringBuilder;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public final class IndexedVars {

	Map<Integer, Set<VarDecl<? extends Type>>> varSets;

	private IndexedVars(final Map<Integer, Set<VarDecl<? extends Type>>> varSets) {
		this.varSets = varSets;
	}

	public Set<VarDecl<? extends Type>> getVars(final int index) {
		Set<VarDecl<? extends Type>> vars = varSets.get(index);
		if (vars == null) {
			vars = Collections.emptySet();
		}
		return Collections.unmodifiableSet(vars);
	}

	public Set<Integer> getNonEmptyIndexes() {
		return varSets.keySet();
	}

	public boolean isEmpty() {
		return varSets.isEmpty();
	}

	public Set<VarDecl<? extends Type>> getAllVars() {
		final Set<VarDecl<? extends Type>> allVars = varSets.values().stream().flatMap(s -> s.stream())
				.collect(Collectors.toSet());
		return Collections.unmodifiableSet(allVars);
	}

	public static Builder builder() {
		return new Builder();
	}

	public static final class Builder {

		private final Map<Integer, Set<VarDecl<? extends Type>>> varSets;
		private boolean built;

		private Builder() {
			varSets = new HashMap<>();
			built = false;
		}

		public void add(final int i, final VarDecl<? extends Type> varDecl) {
			checkState(!built);
			if (!varSets.containsKey(i)) {
				varSets.put(i, new HashSet<>());
			}
			varSets.get(i).add(varDecl);
		}

		public void add(final int i, final Collection<? extends VarDecl<? extends Type>> varDecls) {
			checkState(!built);
			if (!varSets.containsKey(i)) {
				varSets.put(i, new HashSet<>());
			}
			varSets.get(i).addAll(varDecls);
		}

		public void add(final IndexedConstDecl<? extends Type> indexedConstDecl) {
			checkState(!built);
			add(indexedConstDecl.getIndex(), indexedConstDecl.getVarDecl());
		}

		public IndexedVars build() {
			checkState(!built);
			built = true;
			return new IndexedVars(varSets);
		}
	}

	@Override
	public String toString() {
		final ToStringBuilder builder = ObjectUtils.toStringBuilder(getClass().getSimpleName());

		for (final Entry<Integer, Set<VarDecl<? extends Type>>> entry : varSets.entrySet()) {
			final StringJoiner sj = new StringJoiner(", ", entry.getKey() + ": ", "");
			entry.getValue().forEach(v -> sj.add(v.getName()));
			builder.add(sj.toString());
		}
		return builder.toString();
	}
}
