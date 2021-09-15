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
package hu.bme.mit.theta.core.utils;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

public final class StmtUnfoldResult {
	final Collection<Expr<BoolType>> exprs;
	final VarIndexing indexing;

	private StmtUnfoldResult(final Iterable<? extends Expr<BoolType>> exprs, final VarIndexing indexing) {
		this.exprs = ImmutableList.copyOf(exprs);
		this.indexing = indexing;
	}

	public static StmtUnfoldResult of(final Iterable<? extends Expr<BoolType>> exprs, final VarIndexing indexing) {
		return new StmtUnfoldResult(exprs, indexing);
	}

	public Collection<Expr<BoolType>> getExprs() {
		return exprs;
	}

	public VarIndexing getIndexing() {
		return indexing;
	}
}
