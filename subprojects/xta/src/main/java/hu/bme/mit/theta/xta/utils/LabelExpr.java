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
package hu.bme.mit.theta.xta.utils;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;

import java.util.List;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xta.Label;

public final class LabelExpr extends NullaryExpr<Type> {
	private static final int HASH_SEED = 4703;

	private volatile int hashCode = 0;
	private volatile Type type = null;

	private final Label label;

	private LabelExpr(final Label label) {
		this.label = checkNotNull(label);
	}

	public static LabelExpr of(final Label label) {
		return new LabelExpr(label);
	}

	public Label getLabel() {
		return label;
	}

	@Override
	public Type getType() {
		Type result = type;
		if (result == null) {
			result = extractType(label.getParamTypes());
			type = result;
		}
		return result;
	}

	@Override
	public LitExpr<Type> eval(final Valuation val) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + label.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof LabelExpr) {
			final LabelExpr that = (LabelExpr) obj;
			return this.label.equals(that.label);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return label.getName();
	}

	private Type extractType(final List<? extends Type> types) {
		if (types.isEmpty()) {
			return ChanType.getInstance();
		} else {
			final Type head = head(types);
			final List<? extends Type> tail = tail(types);
			return Array(head, extractType(tail));
		}
	}

}
