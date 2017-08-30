package hu.bme.mit.theta.solver.z3.transform;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.Context;

import hu.bme.mit.theta.common.Product2;
import hu.bme.mit.theta.common.Tuple;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.functype.FuncType;

final class Z3DeclTransformer {

	private final Z3TransformationManager transformer;
	private final Z3SymbolTable symbolTable;
	private final Context context;

	Z3DeclTransformer(final Z3TransformationManager transformer, final Z3SymbolTable symbolTable,
			final Context context) {
		this.transformer = transformer;
		this.symbolTable = symbolTable;
		this.context = context;
	}

	public com.microsoft.z3.FuncDecl toSymbol(final Decl<?> decl) {
		if (decl instanceof ConstDecl) {
			return transformConst((ConstDecl<?>) decl);
		} else if (decl instanceof ParamDecl) {
			return transformParam((ParamDecl<?>) decl);
		} else {
			throw new UnsupportedOperationException("Cannot transform declaration: " + decl);
		}
	}

	private com.microsoft.z3.FuncDecl transformConst(final ConstDecl<?> decl) {
		final com.microsoft.z3.FuncDecl symbol;

		if (symbolTable.definesConst(decl)) {
			symbol = symbolTable.getSymbol(decl);
		} else {
			final Type type = decl.getType();

			final Product2<List<Type>, Type> extractedTypes = extractTypes(type);
			final List<Type> paramTypes = extractedTypes._1();
			final Type returnType = extractedTypes._2();

			final com.microsoft.z3.Sort returnSort = transformer.toSort(returnType);
			final com.microsoft.z3.Sort[] paramSorts = paramTypes.stream().map(t -> transformer.toSort(t))
					.toArray(size -> new com.microsoft.z3.Sort[size]);

			symbol = context.mkFuncDecl(decl.getName(), paramSorts, returnSort);
			symbolTable.put(decl, symbol);
		}

		return symbol;
	}

	private com.microsoft.z3.FuncDecl transformParam(final ParamDecl<?> decl) {
		final Type type = decl.getType();
		if (type instanceof FuncType<?, ?>) {
			throw new UnsupportedOperationException("Only simple types are supported");
		} else {
			final com.microsoft.z3.Sort sort = transformer.toSort(type);
			return context.mkConstDecl(decl.getName(), sort);
		}
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
			final List<Type> newParamTypes = ImmutableList.<Type>builder().add(paramType).addAll(paramTypes).build();
			final Tuple2<List<Type>, Type> result = Tuple.of(newParamTypes, newResultType);

			return result;
		} else {
			return Tuple.of(ImmutableList.of(), type);
		}
	}

}
