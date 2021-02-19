package hu.bme.mit.theta.xsts.dsl;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.dsl.*;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.*;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;
import org.antlr.v4.runtime.Token;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;
import static java.util.stream.Collectors.toList;

final class XstsExpression {

	private final DynamicScope scope;
	private final SymbolTable typeTable;
	private final ExprContext context;

	public XstsExpression(final DynamicScope scope, final SymbolTable typeTable, final ExprContext context) {
		this.scope = checkNotNull(scope);
		this.typeTable = checkNotNull(typeTable);
		this.context = checkNotNull(context);
	}

	public Expr<?> instantiate(final Env env) {
		final ExprCreatorVisitor visitor = new ExprCreatorVisitor(scope, typeTable, env);
		final Expr<?> expr = context.accept(visitor);
		if (expr == null) {
			throw new AssertionError();
		} else {
			return expr;
		}
	}

	private static final class ExprCreatorVisitor extends XstsDslBaseVisitor<Expr<?>> {

		private DynamicScope currentScope;
		private final SymbolTable typeTable;
		private final Env env;

		private ExprCreatorVisitor(final DynamicScope scope, final SymbolTable typeTable, final Env env) {
			currentScope = checkNotNull(scope);
			this.typeTable = checkNotNull(typeTable);
			this.env = checkNotNull(env);
		}

		@Override
		public Expr<?> visitIteExpr(final IteExprContext ctx) {
			if (ctx.cond != null) {
				final Expr<BoolType> cond = cast(ctx.cond.accept(this), Bool());
				final Expr<?> then = ctx.then.accept(this);
				final Expr<?> elze = ctx.elze.accept(this);
				return Ite(cond, then, elze);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitIffExpr(final IffExprContext ctx) {
			if (ctx.rightOp != null) {
				final Expr<BoolType> leftOp = cast(ctx.leftOp.accept(this), Bool());
				final Expr<BoolType> rightOp = cast(ctx.rightOp.accept(this), Bool());
				return Iff(leftOp, rightOp);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitImplyExpr(final ImplyExprContext ctx) {
			if (ctx.rightOp != null) {
				final Expr<BoolType> leftOp = cast(ctx.leftOp.accept(this), Bool());
				final Expr<BoolType> rightOp = cast(ctx.rightOp.accept(this), Bool());
				return Imply(leftOp, rightOp);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitOrExpr(final OrExprContext ctx) {
			if (ctx.ops.size() > 1) {
				final Stream<Expr<BoolType>> opStream = ctx.ops.stream()
						.map(op -> cast(op.accept(this), Bool()));
				final Collection<Expr<BoolType>> ops = opStream.collect(toList());
				return Or(ops);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitXorExpr(final XorExprContext ctx) {
			if (ctx.rightOp != null) {
				final Expr<BoolType> leftOp = cast(ctx.leftOp.accept(this), Bool());
				final Expr<BoolType> rightOp = cast(ctx.rightOp.accept(this), Bool());
				return Xor(leftOp, rightOp);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitAndExpr(final AndExprContext ctx) {
			if (ctx.ops.size() > 1) {
				final Stream<Expr<BoolType>> opStream = ctx.ops.stream()
						.map(op -> cast(op.accept(this), Bool()));
				final Collection<Expr<BoolType>> ops = opStream.collect(toList());
				return And(ops);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitNotExpr(final NotExprContext ctx) {
			if (ctx.op != null) {
				final Expr<BoolType> op = cast(ctx.op.accept(this), Bool());
				return Not(op);
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitEqualityExpr(final EqualityExprContext ctx) {
			if (ctx.rightOp != null) {
				final Expr<?> leftOp = ctx.leftOp.accept(this);
				final Expr<?> rightOp = ctx.rightOp.accept(this);

				switch (ctx.oper.getType()) {
					case EQ:
						return Eq(leftOp, rightOp);
					case NEQ:
						return Neq(leftOp, rightOp);
					default:
						throw new ParseException(ctx, "Unknown operator");
				}

			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitRelationExpr(final RelationExprContext ctx) {
			if (ctx.rightOp != null) {
				final Expr<?> leftOp = ctx.leftOp.accept(this);
				final Expr<?> rightOp = ctx.rightOp.accept(this);

				switch (ctx.oper.getType()) {
					case LT:
						return Lt(leftOp, rightOp);
					case LEQ:
						return Leq(leftOp, rightOp);
					case GT:
						return Gt(leftOp, rightOp);
					case GEQ:
						return Geq(leftOp, rightOp);
					default:
						throw new ParseException(ctx, "Unknown operator");
				}

			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitAdditiveExpr(final AdditiveExprContext ctx) {
			if (ctx.ops.size() > 1) {
				final Stream<Expr<?>> opStream = ctx.ops.stream().map(op -> op.accept(this));
				final List<Expr<?>> ops = opStream.collect(toList());

				final Expr<?> opsHead = ops.get(0);
				final List<? extends Expr<?>> opsTail = ops.subList(1, ops.size());

				return createAdditiveExpr(opsHead, opsTail, ctx.opers, ctx);
			} else {
				return visitChildren(ctx);
			}
		}

		private Expr<?> createAdditiveExpr(final Expr<?> opsHead, final List<? extends Expr<?>> opsTail,
										   final List<? extends Token> opers, final AdditiveExprContext ctx) {
			checkArgument(opsTail.size() == opers.size());

			if (opsTail.isEmpty()) {
				return opsHead;
			} else {
				final Expr<?> newOpsHead = opsTail.get(0);
				final List<? extends Expr<?>> newOpsTail = opsTail.subList(1, opsTail.size());

				final Token operHead = opers.get(0);
				final List<? extends Token> opersTail = opers.subList(1, opers.size());

				final Expr<?> subExpr = createAdditiveSubExpr(opsHead, newOpsHead, operHead, ctx);

				return createAdditiveExpr(subExpr, newOpsTail, opersTail, ctx);
			}
		}

		private Expr<?> createAdditiveSubExpr(final Expr<?> leftOp, final Expr<?> rightOp, final Token oper,
											  final AdditiveExprContext ctx) {
			switch (oper.getType()) {

				case PLUS:
					return createAddExpr(leftOp, rightOp);

				case MINUS:
					return createSubExpr(leftOp, rightOp);

				default:
					throw new ParseException(ctx, "Unknown operator '" + oper.getText() + "'");
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

		@Override
		public Expr<?> visitMultiplicativeExpr(final MultiplicativeExprContext ctx) {
			if (ctx.ops.size() > 1) {
				final Stream<Expr<?>> opStream = ctx.ops.stream().map(op -> op.accept(this));
				final List<Expr<?>> ops = opStream.collect(toList());

				final Expr<?> opsHead = ops.get(0);
				final List<? extends Expr<?>> opsTail = ops.subList(1, ops.size());

				return createMutliplicativeExpr(opsHead, opsTail, ctx.opers, ctx);
			} else {
				return visitChildren(ctx);
			}

		}

		private Expr<?> createMutliplicativeExpr(final Expr<?> opsHead, final List<? extends Expr<?>> opsTail,
												 final List<? extends Token> opers, final MultiplicativeExprContext ctx) {
			checkArgument(opsTail.size() == opers.size());

			if (opsTail.isEmpty()) {
				return opsHead;
			} else {
				final Expr<?> newOpsHead = opsTail.get(0);
				final List<? extends Expr<?>> newOpsTail = opsTail.subList(1, opsTail.size());

				final Token operHead = opers.get(0);
				final List<? extends Token> opersTail = opers.subList(1, opers.size());

				final Expr<?> subExpr = createMultiplicativeSubExpr(opsHead, newOpsHead, operHead, ctx);

				return createMutliplicativeExpr(subExpr, newOpsTail, opersTail, ctx);
			}
		}

		private Expr<?> createMultiplicativeSubExpr(final Expr<?> leftOp, final Expr<?> rightOp, final Token oper,
													final MultiplicativeExprContext ctx) {
			switch (oper.getType()) {

				case MUL:
					return createMulExpr(leftOp, rightOp);

				case DIV:
					return createDivExpr(leftOp, rightOp);

				case MOD:
					return createModExpr(leftOp, rightOp);

				case REM:
					return createRemExpr(leftOp, rightOp);

				default:
					throw new ParseException(ctx, "Unknown operator '" + oper.getText() + "'");
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

		private DivExpr<?> createDivExpr(final Expr<?> leftOp, final Expr<?> rightOp) {
			return Div(leftOp, rightOp);
		}

		private ModExpr<?> createModExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
			return Mod(uncastLeftOp, uncastRightOp);
		}

		private RemExpr<?> createRemExpr(final Expr<?> uncastLeftOp, final Expr<?> uncastRightOp) {
			return Rem(uncastLeftOp, uncastRightOp);
		}

		@Override
		public Expr<?> visitUnaryExpr(final UnaryExprContext ctx) {
			if (ctx.op != null) {
				final Expr<?> op = ctx.op.accept(this);
				switch(ctx.oper.getType()) {
					case PLUS:
						return Pos(op);

					case MINUS:
						return Neg(op);

					default:
						throw new ParseException(ctx, "Unknown operator");
				}
			} else {
				return visitChildren(ctx);
			}
		}

		@Override
		public Expr<?> visitAccessorExpr(final AccessorExprContext ctx) {
			if (!ctx.accesses.isEmpty()) {
				final Expr<?> op = ctx.op.accept(this);
				return createAccessExpr(op, ctx.accesses);
			} else {
				return visitChildren(ctx);
			}
		}

		private Expr<?> createAccessExpr(final Expr<?> op, final List<AccessContext> accesses) {
			if (accesses.isEmpty()) {
				return op;
			} else {
				final AccessContext access = head(accesses);
				final Expr<?> subExpr = createAccessSubExpr(op, access);
				return createAccessExpr(subExpr, tail(accesses));
			}
		}

		private Expr<?> createAccessSubExpr(final Expr<?> op, final AccessContext access) {
			if (access.readIndex != null) {
				return createArrayReadExpr(op, access.readIndex);
			} else if (access.writeIndex != null) {
				return createArrayWriteExpr(op, access.writeIndex);
			} else {
				throw new ParseException(access, "Unknown expression");
			}
		}

		private <T1 extends Type, T2 extends Type> Expr<?> createArrayReadExpr(final Expr<?> op,
																			   final ArrayReadAccessContext ctx) {
			checkArgument(op.getType() instanceof ArrayType);
			@SuppressWarnings("unchecked") final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
			final Expr<T1> index = cast(ctx.index.accept(this), array.getType().getIndexType());
			return Read(array, index);
		}

		private <T1 extends Type, T2 extends Type> Expr<?> createArrayWriteExpr(final Expr<?> op,
																				final ArrayWriteAccessContext ctx) {
			checkArgument(op.getType() instanceof ArrayType);
			@SuppressWarnings("unchecked") final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
			final Expr<T1> index = cast(ctx.index.accept(this), array.getType().getIndexType());
			final Expr<T2> elem = cast(ctx.elem.accept(this), array.getType().getElemType());
			return Write(array, index, elem);
		}

		@Override
		public TrueExpr visitTrueExpr(final TrueExprContext ctx) {
			return True();
		}

		@Override
		public FalseExpr visitFalseExpr(final FalseExprContext ctx) {
			return False();
		}

		@Override
		public IntLitExpr visitIntLitExpr(final IntLitExprContext ctx) {
			final var value = new BigInteger(ctx.value.getText());
			return Int(value);
		}

		@Override
		public Expr<?> visitArrLitExpr(final ArrLitExprContext ctx) {
			return createArrayLitExpr(ctx);
		}

		@SuppressWarnings("unchecked")
		private <T1 extends Type, T2 extends Type> Expr<?> createArrayLitExpr(final ArrLitExprContext ctx) {
			checkArgument(ctx.indexExpr.size() > 0 || ctx.indexType != null);
			checkArgument(ctx.valueExpr.size() > 0 || ctx.indexType != null);
			checkNotNull(ctx.elseExpr);

			final T1 indexType;
			final T2 valueType;

			if(ctx.indexType != null) {
				indexType = (T1) new XstsType(typeTable,ctx.indexType).instantiate(env);
			}
			else {
				indexType = (T1) ctx.indexExpr.get(0).accept(this).getType();
			}
			valueType = (T2) ctx.elseExpr.accept(this).getType();

			final List<Tuple2<Expr<T1>, Expr<T2>>> elems = IntStream
					.range(0, ctx.indexExpr.size())
					.mapToObj(i -> Tuple2.of(
							cast(ctx.indexExpr.get(i).accept(this), indexType),
							cast(ctx.valueExpr.get(i).accept(this), valueType)
					))
					.collect(Collectors.toUnmodifiableList());

			final Expr<T2> elseExpr = cast(ctx.elseExpr.accept(this), valueType);
			return Array(elems, elseExpr, ArrayType.of(indexType, valueType));
		}

		@Override
		public Expr<?> visitIdExpr(final IdExprContext ctx) {
			Optional<? extends Symbol> optSymbol = currentScope.resolve(ctx.id.getText());
			if (optSymbol.isEmpty()) {
				throw new ParseException(ctx, "Identifier '" + ctx.id.getText() + "' cannot be resolved");
			}
			final Symbol symbol = optSymbol.get();
			final Object val = env.eval(symbol);
			if (val instanceof IntLitExpr) return (IntLitExpr) val;
			else if (val instanceof Decl) {
				final Decl<?> decl = (Decl<?>) val;
				return decl.getRef();
			}
			throw new ParseException(ctx, "Identifier '" + ctx.id.getText() + "' does not refer to a valid expression");

		}

		@Override
		public Expr<?> visitParenExpr(final ParenExprContext ctx) {
			return ctx.op.accept(this);
		}

	}
}
