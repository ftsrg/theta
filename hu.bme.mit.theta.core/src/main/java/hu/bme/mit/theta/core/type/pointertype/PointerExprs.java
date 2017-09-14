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
package hu.bme.mit.theta.core.type.pointertype;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class PointerExprs {

	private PointerExprs() {
	}

	public static <PointedType extends Type> PointerType<PointedType> Pointer(final PointedType pointedType) {
		checkNotNull(pointedType);
		return new PointerType<>(pointedType);
	}

	public static <PointedType extends Type> NullExpr<PointedType> Null() {
		return NullExpr.getInstance();
	}

	public static <PointedType extends Type> NewExpr<PointedType> New(final PointedType pointedType) {
		return new NewExpr<>(pointedType);
	}

	public static <PointedType extends Type> DerefExpr<PointedType> Deref(final Expr<PointerType<PointedType>> op) {
		return new DerefExpr<>(op);
	}

}
