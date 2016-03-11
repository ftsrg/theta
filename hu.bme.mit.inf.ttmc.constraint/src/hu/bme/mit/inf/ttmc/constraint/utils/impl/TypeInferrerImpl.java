package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.Optional;
import java.util.stream.Stream;

import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IffExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.MulExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.OrExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeInferrer;

public class TypeInferrerImpl implements TypeInferrer {

	private final TypeInferrerVisitor visitor;
	
	public TypeInferrerImpl(final TypeFactory typeFactory) {
		checkNotNull(typeFactory);
		visitor = new TypeInferrerVisitor(typeFactory);
	}
	
	@Override
	public <T extends Type> T getType(final Expr<T> expr) {
		checkNotNull(expr);
		return visitor.getType(expr);
	}
	
	////////
	
	protected static class TypeInferrerVisitor implements ExprVisitor<Void, Type> {

		protected final TypeFactory factory;
		
		protected TypeInferrerVisitor(final TypeFactory factory) {
			this.factory = factory;
		}
		
		public <T extends Type> T getType(final Expr<T> expr) {
			final Type visitResult = expr.accept(this, null);
			@SuppressWarnings("unchecked")
			final T result = (T) visitResult;
			return result;
		}
		
		////////
		
		@Override
		public <DeclType extends Type> DeclType visit(ConstRefExpr<DeclType> expr, Void param) {
			return expr.getDecl().getType();
		}

		@Override
		public <DeclType extends Type> DeclType visit(ParamRefExpr<DeclType> expr, Void param) {
			return expr.getDecl().getType();
		}

		@Override
		public BoolType visit(FalseExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(TrueExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(NotExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(ImplyExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(IffExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(AndExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(OrExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(ExistsExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(ForallExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(EqExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(NeqExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(GeqExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(GtExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(LeqExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public BoolType visit(LtExpr expr, Void param) {
			return factory.Bool();
		}

		@Override
		public IntType visit(IntLitExpr expr, Void param) {
			return factory.Int();
		}

		@Override
		public IntType visit(IntDivExpr expr, Void param) {
			return factory.Int();
		}

		@Override
		public IntType visit(RemExpr expr, Void param) {
			return factory.Int();
		}

		@Override
		public IntType visit(ModExpr expr, Void param) {
			return factory.Int();
		}

		@Override
		public RatType visit(RatLitExpr expr, Void param) {
			return factory.Rat();
		}

		@Override
		public RatType visit(RatDivExpr expr, Void param) {
			return factory.Rat();
		}

		@Override
		public <ExprType extends ClosedUnderNeg> ExprType visit(NegExpr<ExprType> expr, Void param) {
			final Expr<? extends ExprType> op = expr.getOp();
			final ExprType opType = getType(op);
			return opType;
		}

		@Override
		public <ExprType extends ClosedUnderSub> ExprType visit(SubExpr<ExprType> expr, Void param) {
			final Expr<? extends ExprType> leftOp = expr.getLeftOp();
			final Expr<? extends ExprType> rightOp = expr.getRightOp();
			final ExprType leftOpType = getType(leftOp);
			final ExprType rightOpType = getType(rightOp);
			final Optional<ExprType> joinResult = TypeUtils.join(factory, rightOpType, leftOpType);
			final ExprType result = joinResult.get();
			return result;
		}

		@Override
		public <ExprType extends ClosedUnderAdd> ExprType visit(AddExpr<ExprType> expr, Void param) {
			final Collection<? extends Expr<? extends ExprType>> ops = expr.getOps();
			checkArgument(ops.size() > 0);
			final Stream<ExprType> types = ops.stream().map(e -> (ExprType) getType(e));
			final ExprType anyType = types.findAny().get();
			final ExprType result = types.reduce(anyType, (t1, t2) -> TypeUtils.join(factory, t1, t2).get());
			return result;
		}

		@Override
		public <ExprType extends ClosedUnderMul> ExprType visit(MulExpr<ExprType> expr, Void param) {
			final Collection<? extends Expr<? extends ExprType>> ops = expr.getOps();
			checkArgument(ops.size() > 0);
			final Stream<ExprType> types = ops.stream().map(e -> (ExprType) getType(e));
			final ExprType anyType = types.findAny().get();
			final ExprType result = types.reduce(anyType, (t1, t2) -> TypeUtils.join(factory, t1, t2).get());
			return result;
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> ElemType visit(ArrayReadExpr<IndexType, ElemType> expr,
				Void param) {
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array = expr.getArray();
			final ArrayType<? super IndexType, ? extends ElemType> arrayType = getType(array);
			final ElemType elemType = arrayType.getElemType();
			return elemType;
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Type visit(ArrayWriteExpr<IndexType, ElemType> expr,
				Void param) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Type visit(FuncLitExpr<ParamType, ResultType> expr,
				Void param) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> ResultType visit(FuncAppExpr<ParamType, ResultType> expr,
				Void param) {
			final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> func = expr.getFunc();
			final FuncType<? super ParamType, ? extends ResultType> funcType = getType(func);
			final ResultType resultType = funcType.getResultType();
			return resultType;
		}

		@Override
		public <ExprType extends Type> Type visit(IteExpr<ExprType> expr, Void param) {
			final Expr<? extends ExprType> then = expr.getThen();
			final Expr<? extends ExprType> elze = expr.getElse();
			final ExprType thenType = getType(then);
			final ExprType elzeType = getType(elze);
			final Optional<ExprType> joinResult = TypeUtils.join(factory, thenType, elzeType);
			final ExprType result = joinResult.get();
			return result;
		}
		
	}

}
