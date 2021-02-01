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
package hu.bme.mit.theta.sts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.sts.dsl.StsDslHelper.createExprList;
import static hu.bme.mit.theta.sts.dsl.StsDslHelper.resolveSts;

import java.util.List;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.sts.dsl.gen.StsDslBaseVisitor;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.DefStsContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.RefStsContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.StsContext;

final class StsCreator {

	private StsCreator() {
	}

	public static StsDefScope createSts(final Scope scope, final Substitution assignment, final StsContext stsContext) {
		return stsContext.accept(new StsCreatorVisitor(scope, assignment));
	}

	private static final class StsCreatorVisitor extends StsDslBaseVisitor<StsDefScope> {
		private final Scope scope;
		private final Substitution assignment;

		private StsCreatorVisitor(final Scope scope, final Substitution assignment) {
			this.scope = checkNotNull(scope);
			this.assignment = checkNotNull(assignment);
		}

		@Override
		public StsDefScope visitDefSts(final DefStsContext ctx) {
			final StsDefScope stsDefScope = StsDefScope.create(scope, assignment, ctx);
			return stsDefScope;
		}

		@Override
		public StsDefScope visitRefSts(final RefStsContext ctx) {
			final StsDeclSymbol symbol = resolveSts(scope, ctx.ref.getText());
			final List<Expr<?>> args = createExprList(scope, assignment, ctx.params);
			return symbol.instantiate(assignment, args);
		}
	}

}
