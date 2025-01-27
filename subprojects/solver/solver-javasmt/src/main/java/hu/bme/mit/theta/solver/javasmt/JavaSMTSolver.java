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
package hu.bme.mit.theta.solver.javasmt;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.impl.StackImpl;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

final class JavaSMTSolver implements UCSolver, Solver {

    private final JavaSMTSymbolTable symbolTable;
    private final JavaSMTTransformationManager transformationManager;
    private final JavaSMTTermTransformer termTransformer;

    private final SolverContext context;
    private final BasicProverEnvironment solver;

    private final Stack<Expr<BoolType>> assertions;

    private Valuation model;
    private Collection<Expr<BoolType>> unsatCore;

    private final Map<String, Expr<BoolType>> assumptions;
    private SolverStatus status;

		private int expCnt = 0;

    public JavaSMTSolver(
            final JavaSMTSymbolTable symbolTable,
            final JavaSMTTransformationManager transformationManager,
            final JavaSMTTermTransformer termTransformer,
            final SolverContext context,
            final BasicProverEnvironment solver) {
        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
        this.context = context;
        this.solver = solver;

        assertions = new StackImpl<>();
        assumptions = Containers.createMap();
    }

    ////

    @Override
    public void add(final Expr<BoolType> assertion) {
        checkNotNull(assertion);
        final BooleanFormula term = (BooleanFormula) transformationManager.toTerm(assertion);
        add(assertion, term);
    }

    Object add(final Expr<BoolType> assertion, final BooleanFormula term) {
        assertions.add(assertion);
        Object ret;
        try {
            ret = solver.addConstraint(term);
        } catch (InterruptedException e) {
            throw new JavaSMTSolverException(e);
        }
        clearState();
        return ret;
    }

    @Override
    public void track(final Expr<BoolType> assertion) {
        add(assertion);
    }

    @Override
    public Collection<Expr<BoolType>> getUnsatCore() {
        checkState(status == SolverStatus.UNSAT, "Cannot get unsat core if status is not UNSAT");

        if (unsatCore == null) {
            unsatCore = extractUnsatCore();
        }

        assert unsatCore != null;
        return Collections.unmodifiableCollection(unsatCore);
    }

    private Collection<Expr<BoolType>> extractUnsatCore() {
        assert status == SolverStatus.UNSAT;
        assert unsatCore == null;

        final Collection<Expr<BoolType>> unsatCore = new LinkedList<>();

        final List<BooleanFormula> jsmtUnsatCore = solver.getUnsatCore();

        for (final Formula term : jsmtUnsatCore) {
            final Expr<BoolType> assumption = (Expr<BoolType>) termTransformer.toExpr(term);

            assert assumption != null;
            unsatCore.add(assumption);
        }

        return unsatCore;
    }

    @Override
    public SolverStatus check() {
        try {
            final boolean unsat = solver.isUnsat();
            status = unsat ? SolverStatus.UNSAT : SolverStatus.SAT;
            return status;
        } catch (SolverException | InterruptedException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    @Override
    public void push() {
				expCnt++;
        assertions.push();
        try {
            solver.push();
        } catch (InterruptedException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    @Override
    public void pop(final int n) {
				expCnt-=n;
        assertions.pop(n);
        for (int i = 0; i < n; i++) {
            solver.pop();
        }
        clearState();
    }
		
		@Override 
		public void popAll() {
				pop(expCnt);
		}

    @Override
    public void reset() {
        throw new JavaSMTSolverException("Cannot reset JavaSMT right now.");
    }

    @Override
    public SolverStatus getStatus() {
        checkState(status != null, "Solver status is unknown.");
        return status;
    }

    @Override
    public Valuation getModel() {
        checkState(status == SolverStatus.SAT, "Cannot get model if status is not SAT.");

        if (model == null) {
            model = extractModel();
        }

        return model;
    }

    private Valuation extractModel() {
        assert status == SolverStatus.SAT;
        assert model == null;

        final Model model;
        try {
            model = solver.getModel();
            return new JavaSMTModel(model);
        } catch (SolverException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return assertions.toCollection();
    }

    private void clearState() {
        status = null;
        model = null;
        unsatCore = null;
    }

    public SolverContext getContext() {
        return context;
    }

    public BasicProverEnvironment getSolver() {
        return solver;
    }

    @Override
    public void close() {
        context.close();
    }

    @Override
    public ImmutableMap<String, String> getStatistics() {
        return solver.getStatistics();
    }

    ////

    private final class JavaSMTModel extends Valuation {

        private final Model model;
        private final Map<Decl<?>, LitExpr<?>> constToExpr;
        private volatile Collection<ConstDecl<?>> constDecls = null;

        public JavaSMTModel(final Model model) {
            this.model = model;
            constToExpr = Containers.createMap();
        }

        @Override
        public Collection<ConstDecl<?>> getDecls() {
            Collection<ConstDecl<?>> result = constDecls;
            if (result == null) {
                result = constDeclsOf(model);
                constDecls = result;
            }
            return result;
        }

        @Override
        public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
            checkNotNull(decl);

            if (!(decl instanceof ConstDecl)) {
                return Optional.empty();
            }

            final ConstDecl<DeclType> constDecl = (ConstDecl<DeclType>) decl;

            LitExpr<?> val = constToExpr.get(constDecl);
            if (val == null) {
                val = extractLiteral(constDecl);
                if (val != null) {
                    constToExpr.put(constDecl, val);
                }
            }

            @SuppressWarnings("unchecked")
            final LitExpr<DeclType> tVal = (LitExpr<DeclType>) val;
            return Optional.ofNullable(tVal);
        }

        private <DeclType extends Type> LitExpr<?> extractLiteral(final ConstDecl<DeclType> decl) {
            final Formula formula = transformationManager.toSymbol(decl);
            final Type type = decl.getType();
            if (type instanceof FuncType) {
                return extractFuncLiteral(formula);
            } else if (type instanceof ArrayType) {
                return extractArrayLiteral(formula);
            } else if (type instanceof BvType) {
                return extractBvConstLiteral(formula);
            } else if (type instanceof EnumType enumType) {
                return extractEnumLiteral(formula, enumType);
            } else {
                return extractConstLiteral(formula);
            }
        }

        private LitExpr<?> extractFuncLiteral(final Formula formula) {
            final Expr<?> expr = termTransformer.toExpr(formula);
            return (LitExpr<?>) expr;
        }

        private LitExpr<?> extractArrayLiteral(final Formula formula) {
            final Expr<?> expr = termTransformer.toExpr(formula);
            return (LitExpr<?>) expr;
        }

        private LitExpr<?> extractBvConstLiteral(final Formula formula) {
            final Formula term = model.eval(formula);
            if (term == null) {
                return null;
            } else {
                return (BvLitExpr) termTransformer.toExpr(term);
            }
        }

        private LitExpr<EnumType> extractEnumLiteral(Formula formula, EnumType enumType) {
            final Formula term = model.eval(formula);
            if (term == null) {
                return null;
            }
            return enumType.litFromLongName(term.toString());
        }

        private LitExpr<?> extractConstLiteral(final Formula formula) {
            final Formula term = model.eval(formula);
            if (term == null) {
                return null;
            } else {
                return (LitExpr<?>) termTransformer.toExpr(term);
            }
        }

        @Override
        public Map<Decl<?>, LitExpr<?>> toMap() {
            getDecls().forEach(this::eval);
            return Collections.unmodifiableMap(constToExpr);
        }

        ////

        private Collection<ConstDecl<?>> constDeclsOf(final Model model) {
            final ImmutableList.Builder<ConstDecl<?>> builder = ImmutableList.builder();
            for (final Formula symbol :
                    model.asList().stream().map(ValueAssignment::getKey).toList()) {
                if (symbolTable.definesSymbol(symbol)) {
                    final ConstDecl<?> constDecl = symbolTable.getConst(symbol);
                    builder.add(constDecl);
                }
            }
            return builder.build();
        }
    }
}
