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
package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.IndexedVars;
import hu.bme.mit.theta.core.utils.IndexedVars.Builder;

/**
 * An interpolant-based refutation that is a sequence of formulas.
 */
public final class ItpRefutation implements Refutation, Iterable<Expr<BoolType>> {

	private final List<Expr<BoolType>> itpSequence;
	private final int pruneIndex;

	private ItpRefutation(final List<Expr<BoolType>> itpSequence) {
		checkNotNull(itpSequence);
		checkArgument(!itpSequence.isEmpty(), "Zero length interpolant sequence size");
		this.itpSequence = ImmutableList.copyOf(itpSequence);
		int i = 0;
		while (i < itpSequence.size() && itpSequence.get(i).equals(True())) {
			++i;
		}
		this.pruneIndex = i;
		assert 0 <= this.pruneIndex && this.pruneIndex < itpSequence.size();
	}

	public static ItpRefutation sequence(final List<Expr<BoolType>> itpSequence) {
		return new ItpRefutation(itpSequence);
	}

	public static ItpRefutation binary(final Expr<BoolType> itp, final int i, final int n) {
		checkNotNull(itp);
		checkArgument(n > 0, "Zero length interpolant");
		checkArgument(0 <= i && i < n, "Formula index out of bounds");
		final List<Expr<BoolType>> itpSequence = new ArrayList<>(n);
		for (int k = 0; k < n; ++k) {
			if (k < i) {
				itpSequence.add(True());
			} else if (k > i) {
				itpSequence.add(False());
			} else {
				itpSequence.add(itp);
			}
		}
		return new ItpRefutation(itpSequence);
	}

	public int size() {
		return itpSequence.size();
	}

	public List<Expr<BoolType>> toList() {
		return itpSequence;
	}

	public Expr<BoolType> get(final int i) {
		checkElementIndex(i, size());
		return itpSequence.get(i);
	}

	@Override
	public Iterator<Expr<BoolType>> iterator() {
		return itpSequence.iterator();
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(itpSequence).toString();
	}

	public Stream<Expr<BoolType>> stream() {
		return itpSequence.stream();
	}

	@Override
	public int getPruneIndex() {
		return pruneIndex;
	}

	public VarsRefutation toVarSetsRefutation() {
		final Builder builder = IndexedVars.builder();
		for (int i = 0; i < itpSequence.size(); ++i) {
			builder.add(i, ExprUtils.getVars(itpSequence.get(i)));
		}
		return VarsRefutation.create(builder.build());
	}
}
