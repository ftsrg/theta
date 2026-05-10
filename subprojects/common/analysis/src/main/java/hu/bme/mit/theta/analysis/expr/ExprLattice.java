/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;

public final class ExprLattice implements Lattice<BasicExprState> {

    public enum MeetImpl {
      BASIC,
      SYNTACTIC_CHECK,
      SEMANTIC_CHECK
    }

    private final PartialOrd<ExprState> partialOrd;
    private final MeetImpl meetImpl;

    private ExprLattice(final Solver solver, final MeetImpl meetImpl) {
        checkNotNull(solver);
        partialOrd = ExprOrd.create(solver);
        this.meetImpl = meetImpl;
    }

    public static ExprLattice create(final Solver solver) {
        return new ExprLattice(solver, MeetImpl.BASIC);
    }

    public static ExprLattice create(final Solver solver, final MeetImpl meetImpl) {
        return new ExprLattice(solver, meetImpl);
    }

    @Override
    public BasicExprState top() {
        return BasicExprState.of(True());
    }

    @Override
    public BasicExprState bottom() {
        return BasicExprState.of(False());
    }

    @Override
    public boolean isLeq(BasicExprState state1, BasicExprState state2) {
      return partialOrd.isLeq(state1, state2);
    }

    @Override
    public BasicExprState join(BasicExprState state1, BasicExprState state2) {
        final Expr<BoolType> orExpr = Or(state1.toExpr(), state2.toExpr());
        return BasicExprState.of(orExpr);
    }

    @Override
    public BasicExprState meet(BasicExprState state1, BasicExprState state2) {
      if (meetImpl == MeetImpl.SEMANTIC_CHECK) {
        if (partialOrd.isLeq(state1, state2)) {
          return state1;
        }
        if (partialOrd.isLeq(state2, state1)) {
          return state2;
        }
      } else if (meetImpl == MeetImpl.SYNTACTIC_CHECK) {
        final Expr<BoolType> expr1 = state1.toExpr();
        final Expr<BoolType> expr2 = state2.toExpr();
        if (ExprUtils.getConjuncts(expr1).contains(expr2)) {
          return BasicExprState.of(expr1);
        }
        if (ExprUtils.getConjuncts(expr2).contains(expr1)) {
          return BasicExprState.of(expr2);
        }
      }
      return BasicExprState.of(And(state1.toExpr(), state2.toExpr()));
    }
}
