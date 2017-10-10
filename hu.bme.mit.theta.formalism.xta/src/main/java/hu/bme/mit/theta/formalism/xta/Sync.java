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
package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.type.Expr;

public final class Sync {

	public enum Kind {
		EMIT, RECV
	}

	private final Expr<ChanType> expr;
	private final Kind kind;

	private Sync(final Expr<ChanType> expr, final Kind kind) {
		this.expr = checkNotNull(expr);
		this.kind = checkNotNull(kind);
	}

	public static Sync emit(final Expr<ChanType> expr) {
		return new Sync(expr, Kind.EMIT);
	}

	public static Sync recv(final Expr<ChanType> expr) {
		return new Sync(expr, Kind.RECV);
	}

	public Expr<ChanType> getExpr() {
		return expr;
	}

	public Kind getKind() {
		return kind;
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public String toString() {
		return kind == Kind.EMIT ? expr + "!" : expr + "?";
	}

}
