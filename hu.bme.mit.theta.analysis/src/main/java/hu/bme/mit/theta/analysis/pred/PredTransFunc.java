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
package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

public final class PredTransFunc implements TransFunc<PredState, ExprAction, PredPrec> {

	private static final String LIT_PREFIX = "__trans_";
	private final Solver solver;
	private final List<ConstDecl<BoolType>> actLits;

	private PredTransFunc(final Solver solver) {
		this.solver = checkNotNull(solver);
		this.actLits = new ArrayList<>();
	}

	public static PredTransFunc create(final Solver solver) {
		return new PredTransFunc(solver);
	}

	@Override
	public Collection<? extends PredState> getSuccStates(final PredState state, final ExprAction action,
			final PredPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final Set<Expr<BoolType>> preds = prec.getPreds();
		while (actLits.size() < preds.size()) {
			actLits.add(Decls.Const(LIT_PREFIX + actLits.size(), BoolExprs.Bool()));
		}

		assert actLits.size() >= preds.size();

		final List<PredState> succStates = new LinkedList<>();
		try (WithPushPop wp = new WithPushPop(solver)) {
			solver.add(PathUtils.unfold(state.toExpr(), 0));
			solver.add(PathUtils.unfold(action.toExpr(), 0));
			final Map<ConstDecl<BoolType>, Expr<BoolType>> litToPred = new HashMap<>();
			int i = 0;
			for (final Expr<BoolType> pred : preds) {
				final ConstDecl<BoolType> actLit = actLits.get(i);
				litToPred.put(actLit, pred);
				++i;
				solver.add(Iff(actLit.getRef(), PathUtils.unfold(pred, action.nextIndexing())));
			}
			while (solver.check().isSat()) {
				final Valuation model = solver.getModel();
				final Set<Expr<BoolType>> succStatePreds = new HashSet<>();
				final List<Expr<BoolType>> feedBack = new LinkedList<>();
				feedBack.add(True());
				for (final Entry<ConstDecl<BoolType>, Expr<BoolType>> entry : litToPred.entrySet()) {
					final Optional<LitExpr<BoolType>> eval = model.eval(entry.getKey());
					if (eval.isPresent()) {
						if (eval.get().equals(True())) {
							succStatePreds.add(entry.getValue());
							feedBack.add(entry.getKey().getRef());
						} else {
							succStatePreds.add(prec.negate(entry.getValue()));
							feedBack.add(Not(entry.getKey().getRef()));
						}
					}
				}
				succStates.add(PredState.of(succStatePreds));
				solver.add(Not(And(feedBack)));
			}
		}

		return succStates;
	}

}
