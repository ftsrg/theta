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
package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Sets;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

final class DbmSignature implements Iterable<VarDecl<RatType>> {

	private final List<VarDecl<RatType>> indexToVar;
	private final Map<VarDecl<RatType>, Integer> varToIndex;

	private DbmSignature(final Iterable<? extends VarDecl<RatType>> vars) {
		checkNotNull(vars);

		final ImmutableList.Builder<VarDecl<RatType>> indexToVarBuilder = ImmutableList.builder();
		final ImmutableMap.Builder<VarDecl<RatType>, Integer> varToIndexBuilder = ImmutableMap.builder();

		final Set<VarDecl<RatType>> addedVars = new HashSet<>();

		indexToVarBuilder.add(ZeroVar.getInstance());
		varToIndexBuilder.put(ZeroVar.getInstance(), addedVars.size());
		addedVars.add(ZeroVar.getInstance());

		for (final VarDecl<RatType> var : vars) {
			if (!addedVars.contains(var)) {
				indexToVarBuilder.add(var);
				varToIndexBuilder.put(var, addedVars.size());
				addedVars.add(var);
			}
		}

		indexToVar = indexToVarBuilder.build();
		varToIndex = varToIndexBuilder.build();
	}

	////

	static DbmSignature over(final Iterable<? extends VarDecl<RatType>> vars) {
		return new DbmSignature(vars);
	}

	public static DbmSignature union(final DbmSignature signature1, final DbmSignature signature2) {
		checkNotNull(signature1);
		checkNotNull(signature2);
		final Iterable<VarDecl<RatType>> vars = Sets.union(signature1.toSet(), signature2.toSet());
		return new DbmSignature(vars);
	}

	public static DbmSignature intersection(final DbmSignature signature1, final DbmSignature signature2) {
		checkNotNull(signature1);
		checkNotNull(signature2);
		final Set<VarDecl<RatType>> vars = Sets.intersection(signature1.toSet(), signature2.toSet());
		return new DbmSignature(vars);
	}

	////

	public List<VarDecl<RatType>> toList() {
		return indexToVar;
	}

	public Set<VarDecl<RatType>> toSet() {
		return varToIndex.keySet();
	}

	@Override
	public Iterator<VarDecl<RatType>> iterator() {
		return indexToVar.iterator();
	}

	////

	public int size() {
		return indexToVar.size();
	}

	public boolean contains(final VarDecl<RatType> var) {
		checkNotNull(var);
		return varToIndex.containsKey(var);
	}

	public int indexOf(final VarDecl<RatType> var) {
		checkArgument(contains(var), "Unknown variable");
		return varToIndex.get(var);
	}

	public VarDecl<RatType> getVar(final int index) {
		checkElementIndex(index, varToIndex.size());
		return indexToVar.get(index);
	}

	////

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(indexToVar).toString();
	}

	////

}
