/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static com.google.common.base.Preconditions.checkNotNull;

public class IfStmt implements Stmt {

    private final Expr<BoolType> cond;
    private final Stmt then;
    private final Stmt elze;

    private static final int HASH_SEED = 361;
    private static final String STMT_LABEL = "if";

    private volatile int hashCode = 0;

    private IfStmt(final Expr<BoolType> cond, final Stmt then, final Stmt elze) {
        this.cond = checkNotNull(cond);
        this.then = checkNotNull(then);
        this.elze = checkNotNull(elze);
    }

    public static IfStmt of(final Expr<BoolType> cond, final Stmt then, final Stmt elze) {
        return new IfStmt(cond, then, elze);
    }

    public static IfStmt of(final Expr<BoolType> cond, final Stmt then) {
        return new IfStmt(cond, then, SkipStmt.getInstance());
    }

    @Override
    public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
        return visitor.visit(this, param);
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + cond.hashCode();
            result = 31 * result + then.hashCode();
            result = 31 * result + elze.hashCode();
            hashCode = result;
        }
        return result;
    }

    public Expr<BoolType> getCond() {
        return cond;
    }

    public Stmt getThen() {
        return then;
    }

    public Stmt getElze() {
        return elze;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final IfStmt that = (IfStmt) obj;
            return this.cond.equals(that.getCond()) &&
                    this.then.equals(that.getThen()) &&
                    this.elze.equals(that.getElze());
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(STMT_LABEL).add(cond).add(then).add(elze).toString();
    }

}