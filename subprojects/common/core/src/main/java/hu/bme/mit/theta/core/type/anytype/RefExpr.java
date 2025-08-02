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
package hu.bme.mit.theta.core.type.anytype;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.rangetype.RangeType;

public final class RefExpr<DeclType extends Type> extends NullaryExpr<DeclType> {

	private static final int HASH_SEED = 167;
	private volatile int hashCode = 0;

	private final Decl<DeclType> decl;

	private RefExpr(final Decl<DeclType> decl) {
		this.decl = checkNotNull(decl);
	}

	public static <DeclType extends Type> RefExpr<DeclType> of(final Decl<DeclType> decl) {
		return new RefExpr<>(decl);
	}

	public Decl<DeclType> getDecl() {
		return decl;
	}

	@Override
	public DeclType getType() {
		final DeclType type = decl.getType();
		if (type instanceof RangeType rangeType) {
			@SuppressWarnings("unchecked") final DeclType correctedType = (DeclType) rangeType.getCorrectedType();
			return correctedType;
		} else if (type instanceof final ArrayType<?, ?> arrayType) {
			@SuppressWarnings("unchecked") final DeclType correctedType = (DeclType) arrayType.getCorrectedType();
			return correctedType;
		}
		return type;
	}

	@Override
	public LitExpr<DeclType> eval(final Valuation val) {
		return val.eval(decl).get();
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + decl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RefExpr) {
			final RefExpr<?> that = (RefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return decl.getName();
	}

}
