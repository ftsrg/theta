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
import static hu.bme.mit.theta.sts.dsl.StsDslHelper.createBoolExpr;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.sts.STS;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.PropDeclContext;

final class PropDeclSymbol implements Symbol {

	private final PropDeclContext propDeclContext;

	private final StsSpecSymbol scope;

	private final String name;

	private PropDeclSymbol(final StsSpecSymbol scope, final PropDeclContext propDeclContext) {
		this.scope = checkNotNull(scope);
		this.propDeclContext = checkNotNull(propDeclContext);
		name = propDeclContext.name.getText();
	}

	public static PropDeclSymbol create(final StsSpecSymbol scope, final PropDeclContext propDeclContext) {
		return new PropDeclSymbol(scope, propDeclContext);
	}

	////

	@Override
	public String getName() {
		return name;
	}

	////

	public STS instantiate(final Substitution assignment) {
		final StsDefScope stsDefScope = StsCreator.createSts(scope, assignment, propDeclContext.system);
		final Expr<BoolType> prop = createBoolExpr(stsDefScope, assignment, propDeclContext.cond);

		final STS sts = stsDefScope.getSts();

		final STS.Builder builder = STS.builder();
		builder.addInit(sts.getInit());
		builder.addTrans(sts.getTrans());
		builder.setProp(prop);
		return builder.build();
	}

}
