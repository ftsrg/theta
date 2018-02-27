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
package hu.bme.mit.theta.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.common.dsl.Environment;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.Sync;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.SyncContext;
import hu.bme.mit.theta.xta.utils.ChanType;
import hu.bme.mit.theta.xta.utils.LabelExpr;

final class XtaSync {

	private final XtaExpression expression;
	private final SyncKind syncKind;

	public XtaSync(final XtaTransition scope, final SyncContext context) {
		checkNotNull(scope);
		checkNotNull(context);
		expression = new XtaExpression(scope, context.fExpression);
		syncKind = context.fRecv != null ? SyncKind.RECV : SyncKind.EMIT;
	}

	public enum SyncKind {
		EMIT, RECV
	}

	public Sync instantiate(final Environment env) {
		final Expr<?> expr = expression.instantiate(env);
		TypeUtils.cast(expr, ChanType.getInstance());

		final List<Expr<?>> args = new ArrayList<>();
		final Label label = extractLabel(expr, args);

		if (syncKind == SyncKind.EMIT) {
			return Sync.emit(label, args);
		} else if (syncKind == SyncKind.RECV) {
			return Sync.recv(label, args);
		} else {
			throw new AssertionError();
		}
	}

	private Label extractLabel(final Expr<?> expr, final List<Expr<?>> args) {
		if (expr instanceof LabelExpr) {
			final LabelExpr labelExpr = (LabelExpr) expr;
			return labelExpr.getLabel();
		} else if (expr instanceof ArrayReadExpr) {
			final ArrayReadExpr<?, ?> arrayReadExpr = (ArrayReadExpr<?, ?>) expr;
			final Expr<?> arrayExpr = arrayReadExpr.getArray();
			final Expr<?> indexExpr = arrayReadExpr.getIndex();
			args.add(indexExpr);
			return extractLabel(arrayExpr, args);
		} else {
			throw new AssertionError();
		}
	}

}
