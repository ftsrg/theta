package hu.bme.mit.inf.ttmc.constraint.z3.decl;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import hu.bme.mit.inf.ttmc.common.Tuple2;
import hu.bme.mit.inf.ttmc.common.Tuples;
import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.type.Z3Type;

public final class Z3ConstDecl<DeclType extends Type> extends AbstractConstDecl<DeclType> implements Z3Decl<DeclType> {

	private final Context context;

	private volatile com.microsoft.z3.FuncDecl symbol;

	private volatile ConstRefExpr<DeclType> ref;

	public Z3ConstDecl(final String name, final DeclType type, final Context context) {
		super(name, type);
		this.context = context;
	}

	@Override
	public ConstRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = new Z3ConstRefExpr<>(this, context);
		}

		return ref;
	}

	@Override
	public com.microsoft.z3.FuncDecl getSymbol() {
		if (symbol == null) {
			final Type type = getType();

			final Tuple2<List<Type>, Type> extractedTypes = extractTypes(type);
			final List<Type> paramTypes = extractedTypes._1();
			final Type returnType = extractedTypes._2();

			final Z3Type z3ReturnType = (Z3Type) returnType;

			final Sort returnSort = z3ReturnType.getSort();
			final Sort[] paramSorts = new Sort[paramTypes.size()];

			int i = 0;
			for (final Type paramType : paramTypes) {
				final Z3Type z3ParamType = (Z3Type) paramType;
				final Sort paramSort = z3ParamType.getSort();
				paramSorts[i] = paramSort;
				i++;
			}

			symbol = context.mkFuncDecl(getName(), paramSorts, returnSort);
		}

		return symbol;
	}

	private Tuple2<List<Type>, Type> extractTypes(final Type type) {
		if (type instanceof FuncType<?, ?>) {
			final FuncType<?, ?> funcType = (FuncType<?, ?>) type;

			final Type paramType = funcType.getParamType();
			final Type resultType = funcType.getResultType();

			checkArgument(!(paramType instanceof FuncType));

			final Tuple2<List<Type>, Type> subResult = extractTypes(resultType);
			final List<Type> paramTypes = subResult._1();
			final Type newResultType = subResult._2();
			final List<Type> newParamTypes = ImmutableList.<Type> builder().add(paramType).addAll(paramTypes).build();
			final Tuple2<List<Type>, Type> result = Tuples.of(newParamTypes, newResultType);

			return result;
		} else {
			return Tuples.of(ImmutableList.of(), type);
		}
	}

}
