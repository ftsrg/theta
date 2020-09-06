/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.model;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;

/**
 * Mutable implementation of a partitioned valuation.
 */
public final class MutablePartitionedValuation extends Valuation {

	private final List<Map<Decl<?>, LitExpr<?>>> declToExpr;

	public MutablePartitionedValuation() {
		this.declToExpr = new ArrayList<>();
	}

	public static MutablePartitionedValuation copyOf(final MutablePartitionedValuation val) {
		final MutablePartitionedValuation result = new MutablePartitionedValuation();
		for(int i = 0; i < val.getPartitions().size(); ++i) {
			int id = result.createPartition();
			val.getPartitions().get(i).forEach((decl, litExpr) -> result.put(id, decl, litExpr));
		}
		return result;
	}

	private int createPartition() {
		declToExpr.add(new LinkedHashMap<>());
		return declToExpr.size()-1;
	}


	public List<Map<Decl<?>, LitExpr<?>>> getPartitions() {
		return Collections.unmodifiableList(declToExpr);
	}

	public MutablePartitionedValuation put(final int id, final Decl<?> decl, final LitExpr<?> value) {
		checkArgument(value.getType().equals(decl.getType()), "Type mismatch.");
		checkArgument(declToExpr.size() > id, "Index out of bounds");
		declToExpr.get(id).put(decl, value);
		return this;
	}

	public MutablePartitionedValuation remove(final int id, final Decl<?> decl) {
		checkArgument(declToExpr.size() > id, "Index out of bounds");
		declToExpr.get(id).remove(decl);
		return this;
	}

	public MutablePartitionedValuation remove(final Decl<?> decl) {
		for(Map<Decl<?>, LitExpr<?>> decls : declToExpr) {
			decls.remove(decl);
		}
		return this;
	}

	public MutablePartitionedValuation clear(){
		declToExpr.clear();
		return this;
	}

	public MutablePartitionedValuation clear(final int id){
		checkArgument(declToExpr.size() > id, "Index out of bounds");
		declToExpr.get(id).clear();
		return this;
	}

	public MutablePartitionedValuation putAll(final int id, final Valuation val){
		checkArgument(declToExpr.size() > id, "Index out of bounds");
		for (final Decl<?> decl : val.getDecls()) {
			declToExpr.get(id).put(decl, val.eval(decl).get());
		}
		return this;
	}

	@Override
	public Collection<Decl<?>> getDecls() {
		Set<Decl<?>> returnSet = new HashSet<>();
		for(Map<Decl<?>, LitExpr<?>> decls : declToExpr) {
			returnSet.addAll(decls.keySet());
		}
		return Collections.unmodifiableSet(returnSet);
	}

	public Collection<Decl<?>> getDecls(final int id) {
		checkArgument(declToExpr.size() > id, "Index out of bounds");
		return Collections.unmodifiableSet(declToExpr.get(id).keySet());
	}

	@Override
	public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
		checkNotNull(decl);
		for(Map<Decl<?>, LitExpr<?>> decls : declToExpr) {
			@SuppressWarnings("unchecked") final LitExpr<DeclType> val = (LitExpr<DeclType>) decls.get(decl);
			if(val != null) return Optional.of(val);;
		}
		return Optional.empty();
	}

	@Override
	// Unsure if properly working
	public Expr<BoolType> toExpr() {
		return SmartBoolExprs.And(getDecls().stream().map(e -> Eq(e.getRef(), eval(e).get()))
				.collect(toImmutableList()));
	}

	@Override
	public Map<Decl<?>, LitExpr<?>> toMap() {
		Map<Decl<?>, LitExpr<?>> ret = new HashMap<>();
		for(Map<Decl<?>, LitExpr<?>> decl : declToExpr) {
			ret.putAll(decl);
		}
		return Collections.unmodifiableMap(ret);
	}

}
