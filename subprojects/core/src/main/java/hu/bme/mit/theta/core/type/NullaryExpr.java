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
package hu.bme.mit.theta.core.type;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

public abstract class NullaryExpr<ExprType extends Type> implements Expr<ExprType> {

	@Override
	public final List<Expr<?>> getOps() {
		return ImmutableList.of();
	}

	@Override
	public final NullaryExpr<ExprType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.isEmpty());
		return this;
	}

	@Override
	public final int getArity() {
		return 0;
	}

}
