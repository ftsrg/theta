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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.common.Utils;

import java.util.List;

public final class NonDetStmt implements Stmt {

    private final List<Stmt> stmts;

    private final Stmt elze;

    private static final int HASH_SEED = 361;
    private static final String STMT_LABEL = "nondet";

    private volatile int hashCode = 0;

    private NonDetStmt(final List<Stmt> stmts, final Stmt elze) {
        if (stmts.isEmpty()) {
            this.stmts = ImmutableList.of(SkipStmt.getInstance());
        } else {
            this.stmts = stmts;
        }
        this.elze = elze; // Null if does not exist
    }

    public static NonDetStmt of(final List<Stmt> stmts) {
        return of(stmts, null);
    }

    public static NonDetStmt of(final List<Stmt> stmts, Stmt elze) {
        return new NonDetStmt(stmts, elze);
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    public Stmt getElze() {
        return elze;
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
            result = 31 * result + stmts.hashCode();
            if (getElze() != null) {
                result = 31 * result + elze.hashCode();
            }
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof NonDetStmt) {
            final NonDetStmt that = (NonDetStmt) obj;
            boolean equalsValue = this.getStmts().equals(that.getStmts());
            if (this.getElze() == null) {
                equalsValue &= that.getElze() == null;
            } else {
                equalsValue &= this.getElze().equals(that.getElze());
            }
            return equalsValue;
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        final var str = Utils.lispStringBuilder(STMT_LABEL).addAll(stmts);

        if (getElze() != null) {
            str.add("elze").add(getElze());
        }

        return str.toString();
    }

}
