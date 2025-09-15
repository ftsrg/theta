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
package hu.bme.mit.theta.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.clock.constr.ClockConstr;
import hu.bme.mit.theta.core.clock.constr.ClockConstrs;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class Guard {

    private Guard() {}

    static DataGuard dataGuard(final Expr<BoolType> expr) {
        return new DataGuard(expr);
    }

    static ClockGuard clockGuard(final Expr<BoolType> expr) {
        return new ClockGuard(ClockConstrs.formExpr(expr));
    }

    public abstract Expr<BoolType> toExpr();

    public abstract boolean isDataGuard();

    public abstract boolean isClockGuard();

    public abstract DataGuard asDataGuard();

    public abstract ClockGuard asClockGuard();

    public static final class DataGuard extends Guard {

        private final Expr<BoolType> expr;

        private DataGuard(final Expr<BoolType> expr) {
            this.expr = checkNotNull(expr);
        }

        @Override
        public Expr<BoolType> toExpr() {
            return expr;
        }

        @Override
        public boolean isDataGuard() {
            return true;
        }

        @Override
        public boolean isClockGuard() {
            return false;
        }

        @Override
        public DataGuard asDataGuard() {
            return this;
        }

        @Override
        public ClockGuard asClockGuard() {
            throw new ClassCastException();
        }

        @Override
        public String toString() {
            return expr.toString();
        }
    }

    public static final class ClockGuard extends Guard {

        private final ClockConstr clockConstr;

        private ClockGuard(final ClockConstr clockConstr) {
            this.clockConstr = checkNotNull(clockConstr);
        }

        public ClockConstr getClockConstr() {
            return clockConstr;
        }

        @Override
        public Expr<BoolType> toExpr() {
            return clockConstr.toExpr();
        }

        @Override
        public boolean isDataGuard() {
            return false;
        }

        @Override
        public boolean isClockGuard() {
            return true;
        }

        @Override
        public DataGuard asDataGuard() {
            throw new ClassCastException();
        }

        @Override
        public ClockGuard asClockGuard() {
            return this;
        }

        @Override
        public String toString() {
            return clockConstr.toString();
        }
    }
}
