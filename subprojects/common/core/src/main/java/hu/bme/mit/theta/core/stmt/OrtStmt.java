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
import hu.bme.mit.theta.common.Utils;

import java.util.List;

public final class OrtStmt implements Stmt {

    private final List<Stmt> stmts;

    private static final int HASH_SEED = 241;
    private static final String STMT_LABEL = "ort";

    private volatile int hashCode = 0;

    private OrtStmt(final List<Stmt> stmts) {
        if (stmts.isEmpty()) {
            this.stmts = ImmutableList.of(SkipStmt.getInstance());
        } else {
            this.stmts = stmts;
        }
    }

    public static OrtStmt of(final List<Stmt> stmts) {
        return new OrtStmt(stmts);
    }

    public List<Stmt> getStmts() {
        return stmts;
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
            result = 62 * result + stmts.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final OrtStmt that = (OrtStmt) obj;
            return this.getStmts().equals(that.getStmts());
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(STMT_LABEL).addAll(stmts).toString();
    }

}