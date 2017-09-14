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

import static com.google.common.collect.ImmutableList.toImmutableList;

import java.util.List;
import java.util.function.Function;

import hu.bme.mit.theta.core.model.Valuation;

public interface Expr<ExprType extends Type> {

	int getArity();

	ExprType getType();

	LitExpr<ExprType> eval(Valuation val);

	List<? extends Expr<?>> getOps();

	Expr<ExprType> withOps(List<? extends Expr<?>> ops);

	public default Expr<ExprType> map(final Function<? super Expr<?>, ? extends Expr<?>> function) {
		return withOps(getOps().stream().map(op -> function.apply(op)).collect(toImmutableList()));
	}

}
