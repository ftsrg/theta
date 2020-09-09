/*
 *  Copyright 2017 Budapest University of Technology and Economics
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

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xta.Label;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslBaseVisitor;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.*;
import hu.bme.mit.theta.xta.utils.LabelExpr;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neg;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static java.util.stream.Collectors.toList;

final class XtaExpression {

    private final Scope scope;
    private final ExpressionContext context;

    public XtaExpression(final Scope scope, final ExpressionContext context) {
        this.scope = checkNotNull(scope);
        this.context = checkNotNull(context);
    }

    public Expr<?> instantiate(final Env env) {
        final ExpressionInstantiationVisitor visitor = new ExpressionInstantiationVisitor(scope, env);
        final Expr<?> expr = context.accept(visitor);
        final Expr<?> simplifiedExpr = ExprUtils.simplify(expr);
        return simplifiedExpr;
    }

    static final class ExpressionInstantiationVisitor extends XtaDslBaseVisitor<Expr<?>> {
        private final Scope scope;
        private final Env env;

        public ExpressionInstantiationVisitor(final Scope scope, final Env env) {
            this.scope = checkNotNull(scope);
            this.env = checkNotNull(env);
        }

        @Override
        public Expr<?> visitParenthesisExpression(final ParenthesisExpressionContext ctx) {
            return ctx.fOp.accept(this);
        }

        @Override
        public Expr<?> visitNatExpression(final NatExpressionContext ctx) {
            final var value = new BigInteger(ctx.fValue.getText());
            return Int(value);
        }

        @Override
        public Expr<?> visitTrueExpression(final TrueExpressionContext ctx) {
            return True();
        }

        @Override
        public Expr<?> visitFalseExpression(final FalseExpressionContext ctx) {
            return False();
        }

        @Override
        public Expr<?> visitIdExpression(final IdExpressionContext ctx) {
            final String name = ctx.fId.getText();
            Optional<? extends Symbol> optSymbol = scope.resolve(name);
            if (optSymbol.isEmpty()) throw new NoSuchElementException("Identifier '" + name + "' not found");
            final Symbol symbol = optSymbol.get();

            if (env.isDefined(symbol)) {
                // A variable, synchronization label, or a constant already defined
                final Object value = env.eval(symbol);
                if (value instanceof Decl<?>) {
                    final Decl<?> decl = (Decl<?>) value;
                    return decl.getRef();
                } else if (value instanceof Label) {
                    final Label label = (Label) value;
                    return LabelExpr.of(label);
                } else if (value instanceof LitExpr) {
                    final LitExpr<?> expr = (LitExpr<?>) value;
                    return expr;
                } else {
                    throw new AssertionError();
                }

            } else {
                // A constant, whose value is not yet defined, as this is its first occurrence
                final XtaVariableSymbol variableSymbol = (XtaVariableSymbol) symbol;
				assert variableSymbol.isConstant();
				final Object value = env.compute(variableSymbol, v -> v.instantiate("", env).asConstant().getExpr());
				final LitExpr<?> expr = (LitExpr<?>) value;
				return expr;
            }
        }

        @Override
        public Expr<?> visitAdditiveExpression(final AdditiveExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Stream<Expr<?>> opStream = ctx.fOps.stream().map(op -> op.accept(this));
                final List<Expr<?>> ops = opStream.collect(toList());

                final Expr<?> opsHead = ops.get(0);
                final List<? extends Expr<?>> opsTail = ops.subList(1, ops.size());

                return createAdditiveExpr(opsHead, opsTail, ctx.fOpers);
            }
        }

        private Expr<?> createAdditiveExpr(final Expr<?> opsHead, final List<? extends Expr<?>> opsTail,
                                           final List<AdditiveOpContext> opers) {
            checkArgument(opsTail.size() == opers.size());

            if (opsTail.isEmpty()) {
                return opsHead;
            } else {
                final Expr<?> newOpsHead = opsTail.get(0);
                final List<? extends Expr<?>> newOpsTail = opsTail.subList(1, opsTail.size());

                final AdditiveOpContext operHead = opers.get(0);
                final List<AdditiveOpContext> opersTail = opers.subList(1, opers.size());

                final Expr<?> subExpr = createAdditiveSubExpr(opsHead, newOpsHead, operHead);

                return createAdditiveExpr(subExpr, newOpsTail, opersTail);
            }
        }

        private Expr<?> createAdditiveSubExpr(final Expr<?> leftOp, final Expr<?> rightOp,
                                              final AdditiveOpContext oper) {
            if (oper.fAddOp != null) {
                return createAddExpr(leftOp, rightOp);
            } else if (oper.fSubOp != null) {
                return createSubExpr(leftOp, rightOp);
            } else {
                throw new AssertionError();
            }
        }

        private AddExpr<?> createAddExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
            if (leftOp instanceof AddExpr) {
                final AddExpr<?> addLeftOp = (AddExpr<?>) leftOp;
                final List<Expr<?>> ops = ImmutableList.<Expr<?>>builder().addAll(addLeftOp.getOps()).add(rightOp)
                        .build();
                return Add(ops);
            } else {
                return Add(leftOp, rightOp);
            }
        }

        private SubExpr<?> createSubExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
            return Sub(leftOp, rightOp);
        }

        ////////

        @Override
        public Expr<?> visitMultiplicativeExpression(final MultiplicativeExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Stream<Expr<?>> opStream = ctx.fOps.stream().map(op -> op.accept(this));
                final List<Expr<?>> ops = opStream.collect(toList());

                final Expr<?> opsHead = ops.get(0);
                final List<? extends Expr<?>> opsTail = ops.subList(1, ops.size());

                return createMutliplicativeExpr(opsHead, opsTail, ctx.fOpers);
            }
        }

        private Expr<?> createMutliplicativeExpr(final Expr<?> opsHead, final List<? extends Expr<?>> opsTail,
                                                 final List<MultiplicativeOpContext> opers) {
            checkArgument(opsTail.size() == opers.size());

            if (opsTail.isEmpty()) {
                return opsHead;
            } else {
                final Expr<?> newOpsHead = opsTail.get(0);
                final List<? extends Expr<?>> newOpsTail = opsTail.subList(1, opsTail.size());

                final MultiplicativeOpContext operHead = opers.get(0);
                final List<MultiplicativeOpContext> opersTail = opers.subList(1, opers.size());

                final Expr<?> subExpr = createMultiplicativeSubExpr(opsHead, newOpsHead, operHead);

                return createMutliplicativeExpr(subExpr, newOpsTail, opersTail);
            }
        }

        private Expr<?> createMultiplicativeSubExpr(final Expr<?> leftOp, final Expr<?> rightOp,
                                                    final MultiplicativeOpContext oper) {
            if (oper.fMulOp != null) {
                return createMulExpr(leftOp, rightOp);
            } else if (oper.fDivOp != null) {
                return createDivExpr(leftOp, rightOp);
            } else if (oper.fRemOp != null) {
                return createModExpr(leftOp, rightOp);
            } else {
                throw new AssertionError();
            }
        }

        private MulExpr<?> createMulExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
            if (leftOp instanceof MulExpr) {
                final MulExpr<?> addLeftOp = (MulExpr<?>) leftOp;
                final List<Expr<?>> ops = ImmutableList.<Expr<?>>builder().addAll(addLeftOp.getOps()).add(rightOp)
                        .build();
                return Mul(ops);
            } else {
                return Mul(leftOp, rightOp);
            }
        }

        private DivExpr<?> createDivExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
            final Expr<IntType> leftOp = TypeUtils.cast(uncastLeftOp, Int());
            final Expr<IntType> rightOp = TypeUtils.cast(uncastRightOp, Int());
            return Div(leftOp, rightOp);
        }

        private IntModExpr createModExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
            final Expr<IntType> leftOp = TypeUtils.cast(uncastLeftOp, Int());
            final Expr<IntType> rightOp = TypeUtils.cast(uncastRightOp, Int());
            return Mod(leftOp, rightOp);
        }

        ////////

        @Override
        public Expr<?> visitEqualityExpression(final EqualityExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Expr<?> leftOp = ctx.fOps.get(0).accept(this);
                final Expr<?> rightOp = ctx.fOps.get(1).accept(this);

                final EqualityOpContext op = Utils.singleElementOf(ctx.fOpers);
                if (op.fEqOp != null) {
                    return Eq(leftOp, rightOp);
                } else if (op.fNeqOp != null) {
                    return Neq(leftOp, rightOp);
                } else {
                    throw new AssertionError();
                }
            }
        }

        @Override
        public Expr<?> visitRelationalExpression(final RelationalExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Expr<?> leftOp = ctx.fOps.get(0).accept(this);
                final Expr<?> rightOp = ctx.fOps.get(1).accept(this);

                final RelationalOpContext op = Utils.singleElementOf(ctx.fOpers);
                if (op.fLtOp != null) {
                    return Lt(leftOp, rightOp);
                } else if (op.fLeqOp != null) {
                    return Leq(leftOp, rightOp);
                } else if (op.fGtOp != null) {
                    return Gt(leftOp, rightOp);
                } else if (op.fGeqOp != null) {
                    return Geq(leftOp, rightOp);
                } else {
                    throw new AssertionError();
                }
            }
        }

        @Override
        public Expr<?> visitPrefixExpression(final PrefixExpressionContext ctx) {
            if (ctx.fOper == null) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Expr<?> op = ctx.fOp.accept(this);

                final PrefixOpContext oper = ctx.fOper;
                if (oper.fLogNotOp != null) {
                    return Not(TypeUtils.cast(op, Bool()));
                } else if (oper.fPlusOp != null) {
                    return op;
                } else if (oper.fMinusOp != null) {
                    if (op instanceof IntLitExpr) {
                        final IntLitExpr intLitOp = (IntLitExpr) op;
                        return intLitOp.neg();
                    } else if (op instanceof RatLitExpr) {
                        final RatLitExpr ratLitOp = (RatLitExpr) op;
                        return ratLitOp.neg();
                    } else {
                        return Neg(op);
                    }
                } else {
                    // TODO Auto-generated method stub
                    throw new UnsupportedOperationException("TODO: auto-generated method stub");
                }

            }
        }

        @Override
        @SuppressWarnings("unchecked")
        public Expr<?> visitPostfixExpression(final PostfixExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Expr<?> op = ctx.fOp.accept(this);

                final PostfixOpContext oper = Utils.singleElementOf(ctx.fOpers);
                if (oper.fArrayAccessOp != null) {
                    final Expr<?> index = oper.fArrayAccessOp.fExpression.accept(this);
                    return Read((Expr<ArrayType<Type, Type>>) op, (Expr<Type>) index);
                } else {
                    throw new AssertionError();
                }
            }
        }

        @Override
        public Expr<?> visitLogicalAndExpression(final LogicalAndExpressionContext ctx) {
            if (ctx.fOps.size() == 1) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Stream<Expr<BoolType>> opStream = ctx.fOps.stream()
                        .map(op -> TypeUtils.cast(op.accept(this), Bool()));
                final Collection<Expr<BoolType>> ops = opStream.collect(toList());
                return And(ops);
            }
        }

        @Override
        public Expr<?> visitLogicalOrExpression(final LogicalOrExpressionContext ctx) {
            if (ctx.fOps.size() == 1) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Stream<Expr<BoolType>> opStream = ctx.fOps.stream()
                        .map(op -> TypeUtils.cast(op.accept(this), Bool()));
                final Collection<Expr<BoolType>> ops = opStream.collect(toList());
                return Or(ops);
            }
        }

        @Override
        public Expr<?> visitShiftExpression(final ShiftExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return checkNotNull(visitChildren(ctx));
            } else {
                // TODO Auto-generated method stub
                throw new UnsupportedOperationException("TODO: auto-generated method stub");
            }
        }

        @Override
        public Expr<?> visitAssignmentExpression(final AssignmentExpressionContext ctx) {
            if (ctx.fOper == null) {
                return checkNotNull(visitChildren(ctx));
            } else {
                throw new UnsupportedOperationException();
            }
        }

        @Override
        public Expr<?> visitForallExpression(final ForallExpressionContext ctx) {
            // TODO Auto-generated method stub
            throw new UnsupportedOperationException("TODO: auto-generated method stub");
        }

        @Override
        public Expr<?> visitExistsExpression(final ExistsExpressionContext ctx) {
            // TODO Auto-generated method stub
            throw new UnsupportedOperationException("TODO: auto-generated method stub");
        }

        @Override
        public Expr<?> visitTextAndExpression(final TextAndExpressionContext ctx) {
            if (ctx.fOps.size() == 1) {
                return visitChildren(ctx);
            } else {
                // TODO Auto-generated method stub
                throw new UnsupportedOperationException("TODO: auto-generated method stub");
            }
        }

        @Override
        public Expr<?> visitTextOrImplyExpression(final TextOrImplyExpressionContext ctx) {
            if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
                return checkNotNull(visitChildren(ctx));
            } else {
                // TODO Auto-generated method stub
                throw new UnsupportedOperationException("TODO: auto-generated method stub");
            }
        }

        @Override
        public Expr<?> visitTextNotExpression(final TextNotExpressionContext ctx) {
            if (ctx.fOp == null) {
                return checkNotNull(visitChildren(ctx));
            } else {
                // TODO Auto-generated method stub
                throw new UnsupportedOperationException("TODO: auto-generated method stub");
            }
        }

        @Override
        public Expr<?> visitConditionalExpression(final ConditionalExpressionContext ctx) {
            if (ctx.fThenOp == null) {
                return checkNotNull(visitChildren(ctx));
            } else {
                final Expr<BoolType> condOp = TypeUtils.cast(ctx.fCondOp.accept(this), Bool());
                final Expr<?> thenOp = ctx.fThenOp.accept(this);
                final Expr<?> elseOp = ctx.fElseOp.accept(this);
                return Ite(condOp, thenOp, elseOp);
            }
        }

        @Override
        public Expr<?> visitBitwiseOrExpression(final BitwiseOrExpressionContext ctx) {
            if (ctx.fOps.size() == 1) {
                return checkNotNull(visitChildren(ctx));
            } else {
                // TODO Auto-generated method stub
                throw new UnsupportedOperationException("TODO: auto-generated method stub");
            }
        }

        @Override
        public Expr<?> visitBitwiseAndExpression(final BitwiseAndExpressionContext ctx) {
            if (ctx.fOps.size() == 1) {
                return checkNotNull(visitChildren(ctx));
            } else {
                // TODO Auto-generated method stub
                throw new UnsupportedOperationException("TODO: auto-generated method stub");
            }
        }

        @Override
        public Expr<?> visitBitwiseXorExpression(final BitwiseXorExpressionContext ctx) {
            if (ctx.fOps.size() == 1) {
                return checkNotNull(visitChildren(ctx));
            } else {
                // TODO Auto-generated method stub
                throw new UnsupportedOperationException("TODO: auto-generated method stub");
            }
        }
    }

}
