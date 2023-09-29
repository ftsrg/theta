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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.anytype.DeRefExpr;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 *
 */
public final class PointerDereffedStmt implements Stmt {

    private static final int HASH_SEED = 930;
    private static final String STMT_LABEL = "ptrdereffed";

    private final DeRefExpr<?> deRefExpr;

    private final VarDecl<?> varDeclTo;

    private volatile int hashCode = 0;

    private PointerDereffedStmt(final DeRefExpr<?> deRefExpr, final VarDecl<?> to) {
        this.deRefExpr = checkNotNull(deRefExpr);
        this.varDeclTo = checkNotNull(to);
    }

    public static PointerDereffedStmt of(final DeRefExpr<?> deRefExpr, final VarDecl<?> to) {
        return new PointerDereffedStmt(deRefExpr, to);
    }

    public DeRefExpr<?> getDeRefExpr() {
        return deRefExpr;
    }

    public VarDecl<?> getVarDeclTo() {
        return varDeclTo;
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
            result = 31 * result + deRefExpr.hashCode() + varDeclTo.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final PointerDereffedStmt that = (PointerDereffedStmt) obj;
            return this.deRefExpr.equals(that.deRefExpr) && this.varDeclTo.equals(that.varDeclTo);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(STMT_LABEL).add((deRefExpr.toString())).add(" -> ").add(varDeclTo.getName()).toString();
    }
}
