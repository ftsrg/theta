package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.FuncAppExprImpl;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Z3FuncAppExpr<ParamType extends Type, ResultType extends Type>
		extends FuncAppExprImpl<ParamType, ResultType> implements Z3Expr<ResultType> {

	@SuppressWarnings("unused")
	private final Context context;

	@SuppressWarnings("unused")
	private volatile com.microsoft.z3.Expr term;

	public Z3FuncAppExpr(final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> func,
			final Expr<? extends ParamType> param, final Context context) {
		super(func, param);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.Expr getTerm() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

//	@Override
//	public com.microsoft.z3.Expr getTerm() {
//		if (getType() instanceof FuncType<?, ?>) {
//			throw new UnsupportedOperationException();
//		}
//
//		if (term == null) {
//			final Tuple2<ConstRefExpr<?>, List<Expr<?>>> extractedExprs = extractExprs(this);
//			final ConstRefExpr<?> constRef = extractedExprs._1();
//			final List<Expr<?>> params = extractedExprs._2();
//
//			final ConstDecl<?> constDecl = constRef.getDecl();
//			final Z3Decl<?> z3Decl = (Z3Decl<?>) constDecl;
//
//			final com.microsoft.z3.FuncDecl symbol = z3Decl.getSymbol();
//			final com.microsoft.z3.Expr[] paramTerms = new com.microsoft.z3.Expr[params.size()];
//
//			int i = 0;
//			for (Expr<?> param : params) {
//				final Z3Expr<?> z3Param = (Z3Expr<?>) param;
//				final com.microsoft.z3.Expr paramTerm = z3Param.getTerm();
//				paramTerms[i] = paramTerm;
//				i++;
//			}
//
//			term = context.mkApp(symbol, paramTerms);
//		}
//
//		return term;
//	}

//	private Tuple2<ConstRefExpr<?>, List<Expr<?>>> extractExprs(Expr<?> expr) {
//		if (expr instanceof ConstRefExpr<?>) {
//
//			final ConstRefExpr<?> constRef = (ConstRefExpr<?>) expr;
//			return Tuples.of(constRef, ImmutableList.of());
//
//		} else if (expr instanceof FuncAppExpr<?, ?>) {
//
//			final FuncAppExpr<?, ?> appExpr = (FuncAppExpr<?, ?>) expr;
//			final Expr<?> func = appExpr.getFunc();
//			final Expr<?> param = appExpr.getParam();
//
//			checkArgument(!(param.getType() instanceof FuncType));
//
//			final Tuple2<ConstRefExpr<?>, List<Expr<?>>> subResult = extractExprs(func);
//			final List<Expr<?>> params = subResult._2();
//
//			final ConstRefExpr<?> constRef = subResult._1();
//			final List<Expr<?>> newParams = ImmutableList.<Expr<?>> builder().addAll(params).add(param).build();
//
//			return Tuples.of(constRef, newParams);
//		} else {
//			throw new UnsupportedOperationException();
//		}
//	}

}
