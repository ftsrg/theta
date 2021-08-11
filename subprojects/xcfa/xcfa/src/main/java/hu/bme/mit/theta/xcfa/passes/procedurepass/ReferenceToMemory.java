package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.ExpressionReplacer;
import hu.bme.mit.theta.xcfa.model.utils.XcfaStmtUtils;
import hu.bme.mit.theta.xcfa.transformation.grammar.expression.Dereference;
import hu.bme.mit.theta.xcfa.transformation.grammar.expression.Reference;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.compound.CPointer;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class ReferenceToMemory extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		return handleWithGenerics(builder);
	}

	private <P extends Type> XcfaProcedure.Builder handleWithGenerics(XcfaProcedure.Builder builder) {
		Set<RefExpr<?>> referencedVariables = XcfaMetadata.lookupMetadata("referenced", true).stream().map(o -> (RefExpr<?>) o).collect(Collectors.toSet());
		Expr<?> unifiedMemoryMap = null;
		CComplexType fitsall = CComplexType.getFitsall();
		CComplexType ptr = new CPointer(null, null);
		VarDecl<?> placeholderVariable = Var("placeholder", ptr.getSmtType());

		Set<RefExpr<?>> dereferenced = XcfaMetadata.lookupMetadata("dereferenced", true).stream().map(o -> (RefExpr<?>) o).collect(Collectors.toSet());
		for (RefExpr<?> refExpr : dereferenced) {
			addDereferencedToPointers(refExpr);
		}

		Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> dereferencedLut = new LinkedHashMap<>();
		for (RefExpr<?> referencedVariable : referencedVariables) {
			Expr<?> expr;

			Optional<Object> ptrValueOpt = XcfaMetadata.getMetadataValue(referencedVariable, "ptrValue");
			checkState(ptrValueOpt.isPresent() && ptrValueOpt.get() instanceof Integer, "pointer value must be integer!");
			int ptrValue = (int) ptrValueOpt.get();
			//noinspection unchecked
			LitExpr<P> ptrExpr = (LitExpr<P>) ptr.getValue(String.valueOf(ptrValue));
			Type type = CComplexType.getType(referencedVariable).getSmtType();

			Optional<Object> dereferencedOpt = XcfaMetadata.getMetadataValue(referencedVariable, "refSubstitute");
			if(dereferencedOpt.isPresent() && dereferencedOpt.get() instanceof VarDecl) {
				//noinspection unchecked
				VarDecl<ArrayType<P, ?>> memoryMap = (VarDecl<ArrayType<P, ?>>) dereferencedOpt.get();
				expr = ArrayReadExpr.of(cast(memoryMap.getRef(), ArrayType.of(ptr.getSmtType(), type)), cast(ptrExpr, ptr.getSmtType()));
				dereferencedLut.put(referencedVariable.getDecl(), Tuple2.of(memoryMap, ptrExpr));
			}
			else {
				checkState(dereferencedOpt.isEmpty(), "Dereferenced variable not annotated with a variable!");
				expr = referencedVariable;
			}

			if(unifiedMemoryMap != null) {
				unifiedMemoryMap = Ite(Eq(ptrExpr, placeholderVariable.getRef()), fitsall.castTo(expr), unifiedMemoryMap);
			} else {
				unifiedMemoryMap = fitsall.castTo(expr);
			}
		}
		XcfaMetadata.create(unifiedMemoryMap, "cType", fitsall);

		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<Stmt> newStmts = new ArrayList<>();
			boolean found = false;
			for (Stmt stmt : edge.getStmts()) {
				found = handleStmt(unifiedMemoryMap, ptr, dereferencedLut, newStmts, found, stmt, placeholderVariable);
			}
			if(found) {
				builder.removeEdge(edge);
				builder.addEdge(new XcfaEdge(edge.getSource(), edge.getTarget(), newStmts));
			}
		}
		return builder;
	}

	private void addDereferencedToPointers(RefExpr<?> refExpr) {
		Optional<Object> pointsTo = XcfaMetadata.getMetadataValue(refExpr, "pointsTo");
		if(pointsTo.isPresent()) {
			Optional<Object> pointsTo2 = XcfaMetadata.getMetadataValue(pointsTo.get(), "dereferenced");
			if(pointsTo2.isEmpty()) {
				XcfaMetadata.create(pointsTo.get(), "dereferenced", true);;
				XcfaMetadata.create(pointsTo.get(), "refSubstitute", XcfaMetadata.getMetadataValue(refExpr, "refSubstitute").get());;
				addDereferencedToPointers((RefExpr<?>) pointsTo.get());
			}
		}
	}

	private <P extends Type> boolean handleStmt(Expr<?> memoryMap, CComplexType ptr, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> dereferencedLut, List<Stmt> newStmts, boolean found, Stmt stmt, VarDecl<?> placeholderVariable) {
		Optional<Stmt> newStmt = XcfaStmtUtils.replaceStmt(stmt, expr -> {
			if (expr instanceof Dereference) {
				Optional<? extends Expr<?>> replaced = ExpressionReplacer.replace(memoryMap, typeExpr -> {
					if (typeExpr.equals(placeholderVariable.getRef())) {
						//noinspection unchecked
						return Optional.of((Expr<Type>)((Dereference<?, ?>) expr).getOp());
					}
					return Optional.empty();
				});
				Expr<?> newExpr;
				if(replaced.isEmpty()) newExpr = memoryMap;
				else newExpr = replaced.get();
				XcfaMetadata.create(newExpr, "cType", CComplexType.getType(memoryMap));
				Expr<?> cast = CComplexType.getType(expr).castTo(newExpr);
				XcfaMetadata.create(cast, "cType", CComplexType.getType(expr));
				return Optional.of(cast(cast, expr.getType()));
			} else if (expr instanceof Reference) {
				LitExpr<?> value = ptr.getValue(String.valueOf(((Reference<?, ?>) expr).getId()));
				XcfaMetadata.create(value, "cType", CComplexType.getType(expr));
				return Optional.of(cast(value, expr.getType()));
			}
			return Optional.empty();
		});
		if(newStmt.isPresent()) {
			found = true;
			newStmts.addAll(XcfaStmtUtils.replaceVarWithArrayItem(newStmt.get(), dereferencedLut));
		}
		else {
			List<Stmt> stmts = XcfaStmtUtils.replaceVarWithArrayItem(stmt, dereferencedLut);
			newStmts.addAll(stmts);
			if(stmts.size() != 1 || !stmts.get(0).equals(stmt)) found = true;
		}
		return found;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
