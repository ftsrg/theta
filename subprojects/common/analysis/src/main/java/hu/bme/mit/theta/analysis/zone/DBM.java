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
package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.*;
import static java.lang.Math.max;
import static java.lang.Math.min;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.clock.constr.*;
import hu.bme.mit.theta.core.clock.op.*;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.IntBinaryOperator;
import java.util.function.IntConsumer;
import java.util.stream.Collectors;

final class DBM {

    private static final IntBinaryOperator ZERO_DBM_VALUES = (x, y) -> Leq(0);
    private static final IntBinaryOperator TOP_DBM_VALUES = BasicDbm::defaultBound;
    private static final IntBinaryOperator BOTTOM_DBM_VALUES = (x, y) -> Leq(-1);

    private final DbmSignature signature;
    private final BasicDbm dbm;

    private DBM(final DbmSignature signature, final IntBinaryOperator values) {
        this.signature = signature;
        this.dbm = new BasicDbm(signature.size(), values);
    }

    private DBM(final DbmSignature signature, final BasicDbm dbm) {
        checkNotNull(signature);
        checkNotNull(dbm);
        checkArgument(signature.size() == dbm.size(), "Signature and DBM has different size");
        this.signature = signature;
        this.dbm = dbm;
    }

    // TODO replace BiFunction by IntBiFunction
    private DBM(
            final DbmSignature signature,
            final BiFunction<? super VarDecl<RatType>, ? super VarDecl<RatType>, ? extends Integer>
                    values) {
        this(
                signature,
                (final int x, final int y) -> {
                    return values.apply(signature.getVar(x), signature.getVar(y));
                });
    }

    private DBM(final DBM dbm) {
        this.signature = dbm.signature;
        this.dbm = new BasicDbm(dbm.dbm);
    }

    ////

    public Collection<DBM> complement() {
        final Collection<DBM> result = new ArrayList<>();
        if (!dbm.isConsistent()) {
            result.add(DBM.top(Collections.emptySet()));
        } else {
            for (final VarDecl<RatType> x : signature) {
                for (final VarDecl<RatType> y : signature) {
                    final int bound = get(x, y);
                    if (bound != defaultBound(x, y)) {
                        final int newBound = negate(bound);
                        final DbmSignature newSignature = DbmSignature.over(Arrays.asList(x, y));
                        final BiFunction<VarDecl<RatType>, VarDecl<RatType>, Integer> newValues =
                                (c1, c2) -> (c1 == y && c2 == x) ? newBound : defaultBound(c1, c2);
                        final DBM newDBM = new DBM(newSignature, newValues);
                        result.add(newDBM);
                    }
                }
            }
        }
        return result;
    }

    ////

    public static DBM copyOf(final DBM dbm) {
        checkNotNull(dbm);
        return new DBM(dbm);
    }

    public static DBM zero(final Iterable<? extends VarDecl<RatType>> vars) {
        checkNotNull(vars);
        return new DBM(DbmSignature.over(vars), ZERO_DBM_VALUES);
    }

    public static DBM top(final Iterable<? extends VarDecl<RatType>> vars) {
        checkNotNull(vars);
        return new DBM(DbmSignature.over(vars), TOP_DBM_VALUES);
    }

    public static DBM bottom(final Iterable<? extends VarDecl<RatType>> vars) {
        checkNotNull(vars);
        return new DBM(DbmSignature.over(vars), BOTTOM_DBM_VALUES);
    }

    public static DBM project(final DBM dbm, final Iterable<? extends VarDecl<RatType>> vars) {
        checkNotNull(vars);
        return new DBM(DbmSignature.over(vars), dbm::getOrDefault);
    }

    ////

    public static DBM intersection(final DBM dbm1, final DBM dbm2) {
        checkNotNull(dbm1);
        checkNotNull(dbm2);

        final DbmSignature signature = DbmSignature.union(dbm1.signature, dbm2.signature);
        final BiFunction<VarDecl<RatType>, VarDecl<RatType>, Integer> values =
                (x, y) -> {
                    final int bound1 = dbm1.getOrDefault(x, y);
                    final int bound2 = dbm2.getOrDefault(x, y);
                    return min(bound1, bound2);
                };

        final DBM result = new DBM(signature, values);
        result.close();

        return result;
    }

    public static DBM enclosure(final DBM dbm1, final DBM dbm2) {
        checkNotNull(dbm1);
        checkNotNull(dbm2);

        final DbmSignature signature = DbmSignature.union(dbm1.signature, dbm2.signature);
        final BiFunction<VarDecl<RatType>, VarDecl<RatType>, Integer> values =
                (x, y) -> {
                    final int bound1 = dbm1.getOrDefault(x, y);
                    final int bound2 = dbm2.getOrDefault(x, y);
                    return max(bound1, bound2);
                };

        final DBM result = new DBM(signature, values);
        return result;
    }

    ////

    public static DBM weakInterpolant(final DBM dbmA, final DBM dbmB) {
        checkNotNull(dbmA);
        checkNotNull(dbmB);

        if (!dbmA.isConsistent()) {
            return bottom(Collections.emptySet());
        }

        if (!dbmB.isConsistent()) {
            return top(Collections.emptySet());
        }

        // This implementation assumes that A and B are canonical
        // This restriction can be lifted by summarizing maximal paths
        assert dbmA.isClosed();
        assert dbmB.isClosed();

        final DbmSignature interpolantSignature = interpolantSignature(dbmA, dbmB);
        final BiFunction<VarDecl<RatType>, VarDecl<RatType>, Integer> values =
                (x, y) -> {
                    final int bound1 = dbmA.get(x, y);
                    final int bound2 = dbmB.get(x, y);
                    return min(bound1, bound2);
                };

        final DBM interpolant = new DBM(interpolantSignature, values);
        final int[] cycle = interpolant.dbm.closeItp();

        final DbmSignature signature = signatureFrom(interpolantSignature, cycle);
        final DBM result = new DBM(signature, TOP_DBM_VALUES);

        if (cycle.length == 3) {
            final int x = cycle[0];
            final int y = cycle[1];
            final VarDecl<RatType> leftVar = interpolantSignature.getVar(x);
            final VarDecl<RatType> rightVar = interpolantSignature.getVar(y);
            final int boundA1 = dbmA.get(leftVar, rightVar);
            final int boundB1 = dbmB.get(leftVar, rightVar);
            if (boundA1 < boundB1) {
                final int boundB = dbmB.get(rightVar, leftVar);
                result.set(leftVar, rightVar, negate(boundB));
            } else {
                final int boundA2 = dbmA.get(rightVar, leftVar);
                final int boundB2 = dbmB.get(rightVar, leftVar);
                final int boundB = dbmB.get(leftVar, rightVar);
                assert boundA2 < boundB2;
                result.set(rightVar, leftVar, negate(boundB));
            }
        } else {
            // Can this be the case for timed automata?
            for (int i = 0; i + 1 < cycle.length; i++) {
                final int x = cycle[i];
                final int y = cycle[i + 1];
                final VarDecl<RatType> leftVar = interpolantSignature.getVar(x);
                final VarDecl<RatType> rightVar = interpolantSignature.getVar(y);
                final int boundA = dbmA.get(leftVar, rightVar);
                final int boundB = dbmB.get(leftVar, rightVar);
                if (boundA < boundB) {
                    result.set(leftVar, rightVar, boundA);
                }
            }
        }

        assert result.isClosed();
        assert dbmA.getRelation(result).isLeq();
        assert !dbmB.isConsistentWith(result);

        return result;
    }

    public static DBM interpolant(final DBM dbmA, final DBM dbmB) {
        checkNotNull(dbmA);
        checkNotNull(dbmB);

        if (!dbmA.isConsistent()) {
            return bottom(Collections.emptySet());
        }

        if (!dbmB.isConsistent()) {
            return top(Collections.emptySet());
        }

        // This implementation assumes that A and B are canonical
        // This restriction can be lifted by summarizing maximal paths
        assert dbmA.isClosed();
        assert dbmB.isClosed();

        final DbmSignature interpolantSignature = interpolantSignature(dbmA, dbmB);
        final BiFunction<VarDecl<RatType>, VarDecl<RatType>, Integer> values =
                (x, y) -> {
                    final int bound1 = dbmA.get(x, y);
                    final int bound2 = dbmB.get(x, y);
                    return min(bound1, bound2);
                };

        final DBM interpolant = new DBM(interpolantSignature, values);
        final int[] cycle = interpolant.dbm.closeItp();

        final DbmSignature signature = signatureFrom(interpolantSignature, cycle);
        final DBM result = new DBM(signature, TOP_DBM_VALUES);

        // Can this be the case for timed automata?
        for (int i = 0; i + 1 < cycle.length; i++) {
            final int x = cycle[i];
            final int y = cycle[i + 1];
            final VarDecl<RatType> leftVar = interpolantSignature.getVar(x);
            final VarDecl<RatType> rightVar = interpolantSignature.getVar(y);
            final int boundA = dbmA.get(leftVar, rightVar);
            final int boundB = dbmB.get(leftVar, rightVar);
            if (boundA < boundB) {
                result.set(leftVar, rightVar, boundA);
            }
        }

        assert result.isClosed();
        assert dbmA.getRelation(result).isLeq();
        assert !dbmB.isConsistentWith(result);

        return result;
    }

    private static DbmSignature signatureFrom(
            final DbmSignature interpolantSignature, final int[] cycle) {
        final Collection<VarDecl<RatType>> vars = new ArrayList<>();
        for (int i = 0; i + 1 < cycle.length; i++) {
            final VarDecl<RatType> varDecl = interpolantSignature.getVar(cycle[i]);
            vars.add(varDecl);
        }
        return DbmSignature.over(vars);
    }

    private static DbmSignature interpolantSignature(final DBM dbmA, final DBM dbmB) {
        final Set<VarDecl<RatType>> varsConstrainedByBothDBMS =
                Sets.intersection(dbmA.signature.toSet(), dbmB.signature.toSet()).stream()
                        .filter(c -> dbmA.constrains(c) && dbmB.constrains(c))
                        .collect(Collectors.toSet());
        return DbmSignature.over(varsConstrainedByBothDBMS);
    }

    ////

    private int getOrDefault(final VarDecl<RatType> x, final VarDecl<RatType> y) {
        if (!tracks(x) || !tracks(y)) {
            return defaultBound(x, y);
        } else {
            return get(x, y);
        }
    }

    private void set(final VarDecl<RatType> x, final VarDecl<RatType> y, final int b) {
        checkArgument(tracks(x), "Var not tracked");
        checkArgument(tracks(y), "Var not tracked");
        final int i = signature.indexOf(x);
        final int j = signature.indexOf(y);
        dbm.set(i, j, b);
    }

    private int get(final VarDecl<RatType> x, final VarDecl<RatType> y) {
        checkArgument(tracks(x), "Var not tracked");
        checkArgument(tracks(y), "Var not tracked");
        final int i = signature.indexOf(x);
        final int j = signature.indexOf(y);
        return dbm.get(i, j);
    }

    private static int defaultBound(final VarDecl<RatType> x, final VarDecl<RatType> y) {
        if (x.equals(y)) {
            return Leq(0);
        } else {
            return Inf();
        }
    }

    ////

    private boolean isClosed() {
        return dbm.isClosed();
    }

    public boolean isConsistent() {
        return dbm.isConsistent();
    }

    public boolean isConsistentWith(final DBM dbm) {
        checkNotNull(dbm);
        return intersection(this, dbm).isConsistent();
    }

    public boolean isSatisfied(final ClockConstr constr) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("TODO: auto-generated method stub");
    }

    public DbmRelation getRelation(final DBM that) {
        final Set<VarDecl<RatType>> vars =
                Sets.union(this.signature.toSet(), that.signature.toSet());

        boolean leq = true;
        boolean geq = true;

        for (final VarDecl<RatType> x : vars) {
            for (final VarDecl<RatType> y : vars) {
                leq = leq && this.getOrDefault(x, y) <= that.getOrDefault(x, y);
                geq = geq && this.getOrDefault(x, y) >= that.getOrDefault(x, y);
            }
        }
        return DbmRelation.create(leq, geq);
    }

    public boolean isLeq(final DBM that) {
        final Set<VarDecl<RatType>> vars =
                Sets.union(this.signature.toSet(), that.signature.toSet());

        for (final VarDecl<RatType> x : vars) {
            for (final VarDecl<RatType> y : vars) {
                if (this.getOrDefault(x, y) > that.getOrDefault(x, y)) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean isLeq(final DBM that, final Collection<? extends VarDecl<RatType>> activeVars) {
        final Set<VarDecl<RatType>> vars =
                Sets.union(this.signature.toSet(), that.signature.toSet());

        for (final VarDecl<RatType> x : vars) {
            if (!activeVars.contains(x)) {
                continue;
            }

            for (final VarDecl<RatType> y : vars) {
                if (!activeVars.contains(y)) {
                    continue;
                }

                if (this.getOrDefault(x, y) > that.getOrDefault(x, y)) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean isLeq(final DBM that, final BoundFunc bound) {
        final Set<VarDecl<RatType>> vars =
                Sets.union(this.signature.toSet(), that.signature.toSet());

        if (!this.isConsistent()) {
            return true;
        }

        if (!that.isConsistent()) {
            return false;
        }

        for (final VarDecl<RatType> x : vars) {
            final VarDecl<RatType> zero = ZeroVar.getInstance();

            final int Zx0 = this.get(zero, x);
            final int leqMinusUx = LeqMinusUx(x, bound);

            // Zx0 >= (-Ux, <=)
            if (Zx0 < leqMinusUx) {
                continue;
            }

            for (final VarDecl<RatType> y : vars) {
                final int Zxy = this.get(y, x);
                final int Zpxy = that.get(y, x);

                if (Zpxy >= Zxy) {
                    continue;
                }

                final int ltMinusLy = LtMinusLy(y, bound);

                if (add(Zpxy, ltMinusLy) >= Zx0) {
                    continue;
                }

                return false;
            }
        }
        return true;
    }

    private static final int LeqMinusUx(final VarDecl<RatType> x, final BoundFunc boundFunction) {
        return boundFunction.getUpper(x).map(Ux -> Leq(-Ux)).orElse(Inf());
    }

    private static final int LtMinusLy(final VarDecl<RatType> y, final BoundFunc boundFunction) {
        return boundFunction.getLower(y).map(Ly -> Lt(-Ly)).orElse(Inf());
    }

    public Collection<ClockConstr> getConstrs() {
        final Collection<ClockConstr> result = Containers.createSet();

        for (final VarDecl<RatType> leftVar : signature) {
            for (final VarDecl<RatType> rightVar : signature) {
                final int b = get(leftVar, rightVar);
                final ClockConstr constr = DiffBounds.toConstr(leftVar, rightVar, b);

                if (constr instanceof TrueConstr) {
                    continue;
                } else if (constr instanceof FalseConstr) {
                    return Collections.singleton(constr);
                } else {
                    result.add(constr);
                }
            }
        }

        return result;
    }

    ////

    public void execute(final ClockOp op) {
        checkNotNull(op);
        op.accept(ExecuteVisitor.INSTANCE, this);
    }

    public void up() {
        dbm.up();
    }

    public void down() {
        dbm.down();
    }

    public void nonnegative() {
        dbm.nonnegative();
    }

    public void and(final ClockConstr constr) {
        checkNotNull(constr);
        constr.accept(AndOperationVisitor.INSTANCE, this);
    }

    public void free(final VarDecl<RatType> varDecl) {
        checkNotNull(varDecl);
        checkArgument(!isZeroClock(varDecl), "Var is zero");
        ifTracks(varDecl, dbm::free);
    }

    public void free() {
        dbm.free();
    }

    public void reset(final VarDecl<RatType> varDecl, final int m) {
        checkNotNull(varDecl);
        checkArgument(!isZeroClock(varDecl), "Var is zero");
        ifTracks(varDecl, x -> dbm.reset(x, m));
    }

    public void copy(final VarDecl<RatType> lhs, final VarDecl<RatType> rhs) {
        checkNotNull(lhs);
        checkNotNull(rhs);
        checkArgument(!isZeroClock(lhs), "Var is zero");
        checkArgument(!isZeroClock(rhs), "Var is zero");
        ifTracks(lhs, x -> ifTracksElse(rhs, y -> dbm.copy(x, y), () -> dbm.free(x)));
    }

    public void shift(final VarDecl<RatType> varDecl, final int m) {
        checkNotNull(varDecl);
        checkArgument(!isZeroClock(varDecl), "Var is zero");
        ifTracks(varDecl, x -> dbm.shift(x, m));
    }

    public void norm(final Map<? extends VarDecl<RatType>, ? extends Integer> bounds) {
        final int[] k = new int[signature.size()];
        for (int i = 0; i < signature.size(); i++) {
            final VarDecl<RatType> varDecl = signature.getVar(i);
            final Integer bound = bounds.get(varDecl);
            if (bound != null) {
                k[i] = bound;
            } else {
                k[i] = DiffBounds.getBound(Inf());
            }
        }
        dbm.norm(k);
    }

    private void close() {
        dbm.close();
    }

    ////

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();

        sb.append(String.format("%-12s", ""));
        for (final VarDecl<RatType> varDecl : signature) {
            sb.append(String.format("%-12s", varDecl.getName()));
        }
        sb.append(System.lineSeparator());

        for (final VarDecl<RatType> x : signature) {
            sb.append(String.format("%-12s", x.getName()));
            for (final VarDecl<RatType> y : signature) {
                sb.append(String.format("%-12s", asString(get(x, y))));
            }
            sb.append(System.lineSeparator());
        }
        return sb.toString();
    }

    ////

    private boolean tracks(final VarDecl<RatType> varDecl) {
        checkNotNull(varDecl);
        return signature.contains(varDecl);
    }

    private void ifTracks(final VarDecl<RatType> varDecl, final IntConsumer consumer) {
        if (tracks(varDecl)) {
            final int x = signature.indexOf(varDecl);
            consumer.accept(x);
        }
    }

    private void ifTracksElse(
            final VarDecl<RatType> varDecl, final IntConsumer consumer, final Procedure procedure) {
        if (tracks(varDecl)) {
            final int x = signature.indexOf(varDecl);
            consumer.accept(x);
        } else {
            procedure.execute();
        }
    }

    private boolean constrains(final VarDecl<RatType> varDecl) {
        checkNotNull(varDecl);
        return this.tracks(varDecl) && dbm.constrains(signature.indexOf(varDecl));
    }

    private boolean isZeroClock(final VarDecl<RatType> varDecl) {
        return varDecl.equals(ZeroVar.getInstance());
    }

    ////

    private static final class ExecuteVisitor implements ClockOpVisitor<DBM, Void> {

        private static final ExecuteVisitor INSTANCE = new ExecuteVisitor();

        private ExecuteVisitor() {}

        @Override
        public Void visit(final CopyOp op, final DBM dbm) {
            dbm.copy(op.getVar(), op.getValue());
            return null;
        }

        @Override
        public Void visit(final FreeOp op, final DBM dbm) {
            dbm.free(op.getVar());
            return null;
        }

        @Override
        public Void visit(final GuardOp op, final DBM dbm) {
            dbm.and(op.getConstr());
            return null;
        }

        @Override
        public Void visit(final ResetOp op, final DBM dbm) {
            dbm.reset(op.getVar(), op.getValue());
            return null;
        }

        @Override
        public Void visit(final ShiftOp op, final DBM dbm) {
            dbm.shift(op.getVar(), op.getOffset());
            return null;
        }
    }

    ////

    private static final class AndOperationVisitor implements ClockConstrVisitor<DBM, Void> {

        private static final AndOperationVisitor INSTANCE = new AndOperationVisitor();

        private AndOperationVisitor() {}

        @Override
        public Void visit(final TrueConstr constr, final DBM dbm) {
            return null;
        }

        @Override
        public Void visit(final FalseConstr constr, final DBM dbm) {
            dbm.dbm.and(0, 0, Lt(-1));
            return null;
        }

        @Override
        public Void visit(final UnitLtConstr constr, final DBM dbm) {
            final VarDecl<RatType> varDecl = constr.getVar();
            if (dbm.tracks(varDecl)) {
                final int x = dbm.signature.indexOf(varDecl);
                final int m = constr.getBound();
                dbm.dbm.and(x, 0, Lt(m));
            }
            return null;
        }

        @Override
        public Void visit(final UnitLeqConstr constr, final DBM dbm) {
            final VarDecl<RatType> varDecl = constr.getVar();
            if (dbm.tracks(varDecl)) {
                final int x = dbm.signature.indexOf(varDecl);
                final int m = constr.getBound();
                dbm.dbm.and(x, 0, Leq(m));
            }
            return null;
        }

        @Override
        public Void visit(final UnitGtConstr constr, final DBM dbm) {
            final VarDecl<RatType> varDecl = constr.getVar();
            if (dbm.tracks(varDecl)) {
                final int x = dbm.signature.indexOf(varDecl);
                final int m = constr.getBound();
                dbm.dbm.and(0, x, Lt(-m));
            }
            return null;
        }

        @Override
        public Void visit(final UnitGeqConstr constr, final DBM dbm) {
            final VarDecl<RatType> varDecl = constr.getVar();
            if (dbm.tracks(varDecl)) {
                final int x = dbm.signature.indexOf(varDecl);
                final int m = constr.getBound();
                dbm.dbm.and(0, x, Leq(-m));
            }
            return null;
        }

        @Override
        public Void visit(final UnitEqConstr constr, final DBM dbm) {
            final VarDecl<RatType> varDecl = constr.getVar();
            if (dbm.tracks(varDecl)) {
                final int x = dbm.signature.indexOf(varDecl);
                final int m = constr.getBound();
                dbm.dbm.and(x, 0, Leq(m));
                dbm.dbm.and(0, x, Leq(-m));
            }
            return null;
        }

        @Override
        public Void visit(final DiffLtConstr constr, final DBM dbm) {
            final VarDecl<RatType> leftVar = constr.getLeftVar();
            final VarDecl<RatType> rightVar = constr.getRightVar();
            if (dbm.tracks(leftVar) && dbm.tracks(rightVar)) {
                final int x = dbm.signature.indexOf(leftVar);
                final int y = dbm.signature.indexOf(rightVar);
                final int m = constr.getBound();
                dbm.dbm.and(x, y, Lt(m));
            }
            return null;
        }

        @Override
        public Void visit(final DiffLeqConstr constr, final DBM dbm) {
            final VarDecl<RatType> leftVar = constr.getLeftVar();
            final VarDecl<RatType> rightVar = constr.getRightVar();
            if (dbm.tracks(leftVar) && dbm.tracks(rightVar)) {
                final int x = dbm.signature.indexOf(leftVar);
                final int y = dbm.signature.indexOf(rightVar);
                final int m = constr.getBound();
                dbm.dbm.and(x, y, Leq(m));
            }
            return null;
        }

        @Override
        public Void visit(final DiffGtConstr constr, final DBM dbm) {
            final VarDecl<RatType> leftVar = constr.getLeftVar();
            final VarDecl<RatType> rightVar = constr.getRightVar();
            if (dbm.tracks(leftVar) && dbm.tracks(rightVar)) {
                final int x = dbm.signature.indexOf(leftVar);
                final int y = dbm.signature.indexOf(rightVar);
                final int m = constr.getBound();
                dbm.dbm.and(y, x, Lt(-m));
            }
            return null;
        }

        @Override
        public Void visit(final DiffGeqConstr constr, final DBM dbm) {
            final VarDecl<RatType> leftVar = constr.getLeftVar();
            final VarDecl<RatType> rightVar = constr.getRightVar();
            if (dbm.tracks(leftVar) && dbm.tracks(rightVar)) {
                final int x = dbm.signature.indexOf(leftVar);
                final int y = dbm.signature.indexOf(rightVar);
                final int m = constr.getBound();
                dbm.dbm.and(y, x, Leq(-m));
            }
            return null;
        }

        @Override
        public Void visit(final DiffEqConstr constr, final DBM dbm) {
            final VarDecl<RatType> leftVar = constr.getLeftVar();
            final VarDecl<RatType> rightVar = constr.getRightVar();
            if (dbm.tracks(leftVar) && dbm.tracks(rightVar)) {
                final int x = dbm.signature.indexOf(leftVar);
                final int y = dbm.signature.indexOf(rightVar);
                final int m = constr.getBound();
                dbm.dbm.and(x, y, Leq(m));
                dbm.dbm.and(y, x, Leq(-m));
            }
            return null;
        }

        @Override
        public Void visit(final AndConstr constr, final DBM dbm) {
            for (final ClockConstr atomicConstr : constr.getConstrs()) {
                atomicConstr.accept(this, dbm);
                if (!dbm.dbm.isConsistent()) {
                    return null;
                }
            }
            return null;
        }
    }

    @FunctionalInterface
    private interface Procedure {
        void execute();
    }
}
