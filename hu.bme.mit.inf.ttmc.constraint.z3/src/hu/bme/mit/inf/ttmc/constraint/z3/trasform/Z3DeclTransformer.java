package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.common.Tuple2;
import hu.bme.mit.inf.ttmc.common.Tuples;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.DeclVisitor;

class Z3DeclTransformer {

	private final Z3TransformationManager transformer;
	private final Context context;

	private final Z3DeclTransformerVisitor visitor;

	Z3DeclTransformer(final Z3TransformationManager transformer, final Context context) {
		this.context = context;
		this.transformer = transformer;
		visitor = new Z3DeclTransformerVisitor(transformer, context);
	}

	public com.microsoft.z3.FuncDecl transform(final Decl<?, ?> decl) {
		return decl.accept(visitor, null);
	}

	private class Z3DeclTransformerVisitor implements DeclVisitor<Void, com.microsoft.z3.FuncDecl> {

		private final Map<String, ConstDecl<?>> nameToConst;
		private final Map<ConstDecl<?>, com.microsoft.z3.FuncDecl> constToSymbol;

		private Z3DeclTransformerVisitor(final Z3TransformationManager transformator, final Context context) {
			nameToConst = new HashMap<>();
			constToSymbol = new HashMap<>();
		}

		@Override
		public <DeclType extends Type> com.microsoft.z3.FuncDecl visit(final ConstDecl<DeclType> decl,
				final Void param) {
			checkState(!nameToConst.containsKey(decl.getName()));

			com.microsoft.z3.FuncDecl symbol = constToSymbol.get(decl);

			if (symbol == null) {
				final Type type = decl.getType();

				final Tuple2<List<Type>, Type> extractedTypes = extractTypes(type);
				final List<Type> paramTypes = extractedTypes._1();
				final Type returnType = extractedTypes._2();

				final com.microsoft.z3.Sort returnSort = transformer.transform(returnType);
				final com.microsoft.z3.Sort[] paramSorts = paramTypes.stream().map(t -> transformer.transform(t))
						.toArray(size -> new com.microsoft.z3.Sort[size]);

				symbol = context.mkFuncDecl(decl.getName(), paramSorts, returnSort);
				constToSymbol.put(decl, symbol);
			}

			return symbol;
		}

		@Override
		public <DeclType extends Type> com.microsoft.z3.FuncDecl visit(final ParamDecl<DeclType> decl,
				final Void param) {
			final Type type = decl.getType();
			if (type instanceof FuncType<?, ?>) {
				throw new UnsupportedOperationException("Only simple types are supported");
			} else {
				final com.microsoft.z3.Sort sort = transformer.transform(type);
				return context.mkConstDecl(decl.getName(), sort);
			}
		}

		////

		private Tuple2<List<Type>, Type> extractTypes(final Type type) {
			if (type instanceof FuncType<?, ?>) {
				final FuncType<?, ?> funcType = (FuncType<?, ?>) type;

				final Type paramType = funcType.getParamType();
				final Type resultType = funcType.getResultType();

				checkArgument(!(paramType instanceof FuncType));

				final Tuple2<List<Type>, Type> subResult = extractTypes(resultType);
				final List<Type> paramTypes = subResult._1();
				final Type newResultType = subResult._2();
				final List<Type> newParamTypes = ImmutableList.<Type> builder().add(paramType).addAll(paramTypes)
						.build();
				final Tuple2<List<Type>, Type> result = Tuples.of(newParamTypes, newResultType);

				return result;
			} else {
				return Tuples.of(ImmutableList.of(), type);
			}
		}

	}

}
