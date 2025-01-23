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
package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Objects;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.Dereference;

/**
 * Assignment statement of the form *(DEREF_EXPRESSION) := EXPRESSION. The statement updates the
 * value pointed to by DEREF_EXPRESSION with the result of EXPRESSION.
 *
 * @param <DeclType>
 */
public final class MemoryAssignStmt<
                PtrType extends Type, OffsetType extends Type, DeclType extends Type>
        implements Stmt {

    private static final String STMT_LABEL = "memassign";

    private final Dereference<PtrType, OffsetType, DeclType> deref;
    private final Expr<DeclType> expr;

    private MemoryAssignStmt(
            final Dereference<PtrType, OffsetType, DeclType> deref, final Expr<DeclType> expr) {
        this.deref = checkNotNull(deref);
        this.expr = checkNotNull(expr);
    }

    public static <PtrType extends Type, OffsetType extends Type, DeclType extends Type>
            MemoryAssignStmt<PtrType, OffsetType, DeclType> of(
                    final Dereference<PtrType, OffsetType, DeclType> deref,
                    final Expr<DeclType> expr) {
        return new MemoryAssignStmt<>(deref, expr);
    }

    @SuppressWarnings("unchecked")
    public static <PtrType extends Type, OffsetType extends Type, DeclType extends Type>
            MemoryAssignStmt<PtrType, OffsetType, DeclType> create(
                    final Dereference<PtrType, OffsetType, ?> deref, final Expr<DeclType> expr) {
        final Dereference<PtrType, OffsetType, DeclType> typedDeref =
                (Dereference<PtrType, OffsetType, DeclType>) deref;
        final Expr<DeclType> typedExpr = expr;
        return MemoryAssignStmt.of(typedDeref, typedExpr);
    }

    public Dereference<PtrType, OffsetType, DeclType> getDeref() {
        return deref;
    }

    public Expr<DeclType> getExpr() {
        return expr;
    }

    @Override
    public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
        return visitor.visit(this, param);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(deref, expr);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            return Objects.equal(deref, ((MemoryAssignStmt<?, ?, ?>) obj).deref)
                    && Objects.equal(expr, ((MemoryAssignStmt<?, ?, ?>) obj).expr);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(STMT_LABEL).add(deref).add(expr).toString();
    }
}
