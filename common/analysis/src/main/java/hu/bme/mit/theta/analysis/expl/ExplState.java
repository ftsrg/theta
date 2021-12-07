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
package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class ExplState extends Valuation implements ExprState {

	private ExplState() {
	}

	public static ExplState of(final Valuation val) {
		if (val.getDecls().isEmpty()) {
			return top();
		}
		return new NonBottom(val);
	}

	public static ExplState bottom() {
		return BottomLazyHolder.INSTANCE;
	}

	public static ExplState top() {
		return TopLazyHolder.INSTANCE;
	}

	public abstract Valuation getVal();

	public abstract boolean isLeq(final ExplState that);

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ExplState) {
			final ExplState that = (ExplState) obj;
			return this.toMap().equals(that.toMap()) && this.isBottom() == that.isBottom();
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return super.hashCode() + (isBottom() ? 0 : 1);
	}

	////

	private static final class NonBottom extends ExplState {
		private final Valuation val;

		private NonBottom(final Valuation val) {
			this.val = ImmutableValuation.copyOf(checkNotNull(val));
		}

		@Override
		public Collection<? extends Decl<?>> getDecls() {
			return val.getDecls();
		}

		@Override
		public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
			return val.eval(decl);
		}

		@Override
		public Expr<BoolType> toExpr() {
			return val.toExpr();
		}

		@Override
		public Map<Decl<?>, LitExpr<?>> toMap() {
			return val.toMap();
		}

		////

		@Override
		public Valuation getVal() {
			return val;
		}

		@Override
		public boolean isLeq(final ExplState that) {
			if (that.isBottom()) {
				return false;
			} else {
				return this.getVal().isLeq(that.getVal());
			}
		}

		@Override
		public boolean isBottom() {
			return false;
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder(ExplState.class.getSimpleName()).aligned()
					.addAll(val.getDecls().stream().map(d -> String.format("(%s %s)", d.getName(), eval(d).get())))
					.toString();
		}
	}

	private static final class Bottom extends ExplState {
		@Override
		public Collection<? extends Decl<?>> getDecls() {
			return Collections.emptySet();
		}

		@Override
		public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
			return Optional.empty();
		}

		@Override
		public Expr<BoolType> toExpr() {
			return BoolExprs.False();
		}

		@Override
		public Map<Decl<?>, LitExpr<?>> toMap() {
			return Collections.emptyMap();
		}

		////

		@Override
		public Valuation getVal() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isLeq(final ExplState that) {
			return true;
		}

		@Override
		public boolean isBottom() {
			return true;
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder(ExplState.class.getSimpleName()).add("Bottom").toString();
		}
	}

	private static class BottomLazyHolder {
		static final ExplState INSTANCE = new Bottom();
	}

	private static class TopLazyHolder {
		static final ExplState INSTANCE = new NonBottom(ImmutableValuation.empty());
	}
}
