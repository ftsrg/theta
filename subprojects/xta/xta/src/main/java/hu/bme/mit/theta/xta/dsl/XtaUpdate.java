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
package hu.bme.mit.theta.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xta.dsl.XtaExpression.ExpressionInstantiationVisitor;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslBaseVisitor;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.AssignmentExpressionContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.AssignmentOpContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.ExpressionContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.PostfixExpressionContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.PostfixOpContext;

final class XtaUpdate {

    private final Scope scope;
    private final ExpressionContext context;

    public XtaUpdate(final Scope scope, final ExpressionContext context) {
        this.scope = checkNotNull(scope);
        this.context = checkNotNull(context);
    }

    public AssignStmt<?> instantiate(final Env env) {
        final UpdateInstantiationVisitor visitor = new UpdateInstantiationVisitor(env);
        final AssignStmt<?> result = context.accept(visitor);
        return result;
    }

    private final class UpdateInstantiationVisitor extends XtaDslBaseVisitor<AssignStmt<?>> {

        private final ExpressionInstantiationVisitor visitor;

        public UpdateInstantiationVisitor(final Env env) {
            visitor = new ExpressionInstantiationVisitor(scope, env);
        }

        @Override
        public AssignStmt<?> visitAssignmentExpression(final AssignmentExpressionContext ctx) {
            if (ctx.fOper == null) {
                return visitChildren(ctx);
            } else {
                @SuppressWarnings("unchecked")
                final RefExpr<Type> leftOp = (RefExpr<Type>) ctx.fLeftOp.accept(visitor);
                final VarDecl<Type> varDecl = (VarDecl<Type>) leftOp.getDecl();
                @SuppressWarnings("unchecked")
                final Expr<Type> rightOp = (Expr<Type>) ctx.fRightOp.accept(visitor);

                final AssignmentOpContext op = ctx.fOper;
                if (op.fAssignOp != null) {
                    return Stmts.Assign(varDecl, rightOp);
                } else {
                    // TODO Auto-generated method stub
                    throw new UnsupportedOperationException();
                }
            }
        }

        @Override
        public AssignStmt<?> visitPostfixExpression(final PostfixExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return visitChildren(ctx);
            } else {
                final RefExpr<?> ref = (RefExpr<?>) ctx.fOp.accept(visitor);
                final VarDecl<?> varDecl = (VarDecl<?>) ref.getDecl();
                final VarDecl<IntType> intVar = TypeUtils.cast(varDecl, Int());
                final RefExpr<IntType> intRef = intVar.getRef();

                final PostfixOpContext op = Utils.singleElementOf(ctx.fOpers);
                if (op.fPostIncOp != null) {
                    return Stmts.Assign(intVar, Add(intRef, Int(1)));
                } else if (op.fPostDeclOp != null) {
                    return Stmts.Assign(intVar, Sub(intRef, Int(1)));
                } else {
                    throw new UnsupportedOperationException();
                }
            }
        }
    }
}
