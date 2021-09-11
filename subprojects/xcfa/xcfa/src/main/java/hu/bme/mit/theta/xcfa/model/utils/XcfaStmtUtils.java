package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

public class XcfaStmtUtils {
	/**
	 * Replace expressions in a stmt based on a given Expr -> Opt(Expr) mapping function
	 * @param stmt		Statement to replace expressions in
	 * @param mapper	Mapping function that returns a new Expression when necessary, empty otherwise
	 * @return 			Optional.empty() when no modification was necessary, the new XcfaLabel otherwise
	 */
	public static <T extends Type> Optional<XcfaLabel> replaceStmt(final XcfaLabel stmt, final Function<Expr<T>, Optional<Expr<T>>> mapper) {
		return stmt.accept(new LabelExpressionMappingVisitor<>(), mapper);
	}

	/**
	 * Replace every instance of the declarations in `lookup` with an array read/write reference
	 * @param stmt		The stmt to replace the decls in
	 * @param lookup	The lookup table to use for mapping variables to array items
	 * @param <R>		The index type
	 * @param <T>		The element type
	 * @return			Returns the statement(s) - multiple in the case of a Havoc stmt
	 */
	public static <P extends Type> List<XcfaLabel> replaceVarWithArrayItem(final XcfaLabel stmt, final Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> lookup) {
		return stmt.accept(new StmtVarToArrayItemVisitor<>(), lookup);
	}
}
