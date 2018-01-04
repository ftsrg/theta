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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

/**
 * Utility for generating {@link PredState}s.
 */
public final class PredStates {

	private final Solver solver;
	private final List<ConstDecl<BoolType>> actLits;
	private final String litPrefix;
	private static int instanceCounter = 0;

	public PredStates(final Solver solver) {
		this.solver = checkNotNull(solver);
		this.actLits = new ArrayList<>();
		this.litPrefix = "__actlit" + instanceCounter + "_";
		instanceCounter++;
	}

	public Collection<PredState> createStatesForExpr(final Expr<BoolType> expr, final VarIndexing exprIndexing,
			final PredPrec prec, final VarIndexing precIndexing) {
		checkNotNull(expr);
		checkNotNull(exprIndexing);
		checkNotNull(prec);
		checkNotNull(precIndexing);

		final List<Expr<BoolType>> preds = new ArrayList<>(prec.getPreds());
		generateActivationLiterals(preds.size());

		assert actLits.size() >= preds.size();

		final List<PredState> states = new LinkedList<>();
		try (WithPushPop wp = new WithPushPop(solver)) {
			solver.add(PathUtils.unfold(expr, exprIndexing));
			for (int i = 0; i < preds.size(); ++i) {
				solver.add(Iff(actLits.get(i).getRef(), PathUtils.unfold(preds.get(i), precIndexing)));
			}
			while (solver.check().isSat()) {
				final Valuation model = solver.getModel();
				final Set<Expr<BoolType>> newStatePreds = new HashSet<>();
				final List<Expr<BoolType>> feedback = new LinkedList<>();
				feedback.add(True());
				for (int i = 0; i < preds.size(); ++i) {
					final ConstDecl<BoolType> lit = actLits.get(i);
					final Expr<BoolType> pred = preds.get(i);
					final Optional<LitExpr<BoolType>> eval = model.eval(lit);
					if (eval.isPresent()) {
						if (eval.get().equals(True())) {
							newStatePreds.add(pred);
							feedback.add(lit.getRef());
						} else {
							newStatePreds.add(prec.negate(pred));
							feedback.add(Not(lit.getRef()));
						}
					}
				}
				states.add(PredState.of(newStatePreds));
				solver.add(Not(And(feedback)));
			}
		}

		return states;
	}

	private void generateActivationLiterals(final int n) {
		while (actLits.size() < n) {
			actLits.add(Decls.Const(litPrefix + actLits.size(), BoolExprs.Bool()));
		}
	}
}
