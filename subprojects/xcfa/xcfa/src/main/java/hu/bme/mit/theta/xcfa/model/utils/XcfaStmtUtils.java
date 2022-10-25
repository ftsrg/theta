/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

public class XcfaStmtUtils {
	/**
	 * Replace expressions in a stmt based on a given Expr to Opt(Expr) mapping function
	 *
	 * @param stmt   Statement to replace expressions in
	 * @param mapper Mapping function that returns a new Expression when necessary, empty otherwise
	 * @return Optional.empty() when no modification was necessary, the new XcfaLabel otherwise
	 */
	public static <T extends Type> Optional<XcfaLabel> replaceExprsInStmt(final XcfaLabel stmt, final Function<Expr<?>, Optional<Expr<T>>> mapper) {
		return stmt.accept(new LabelExpressionMappingVisitor<>(), LabelExpressionMappingVisitor.Mapper.create(mapper, v -> Optional.empty()));
	}

	/**
	 * Replace expressions in a stmt based on a given Var to Opt(Var) mapping function
	 *
	 * @param stmt   Statement to replace expressions in
	 * @param mapper Mapping function that returns a new VarDecl when necessary, empty otherwise
	 * @return Optional.empty() when no modification was necessary, the new XcfaLabel otherwise
	 */
	public static <T extends Type> Optional<XcfaLabel> replacesVarsInStmt(final XcfaLabel stmt, final Function<VarDecl<?>, Optional<VarDecl<T>>> mapper) {
		return stmt.accept(new LabelExpressionMappingVisitor<>(), LabelExpressionMappingVisitor.Mapper.create(e -> {
			Optional<VarDecl<T>> vOpt;
			if (e instanceof RefExpr && (vOpt = mapper.apply((VarDecl<T>) ((RefExpr<T>) e).getDecl())).isPresent())
				return Optional.of(vOpt.get().getRef());
			else return Optional.empty();
		}, mapper));
	}

	/**
	 * Replace every instance of the declarations in `lookup` with an array read/write reference
	 *
	 * @param stmt   The stmt to replace the decls in
	 * @param lookup The lookup table to use for mapping variables to array items
	 * @return Returns the statement(s) - multiple in the case of a Havoc stmt
	 */
	public static <P extends Type> List<XcfaLabel> replaceVarWithArrayItem(final XcfaLabel stmt, final Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> lookup) {
		return stmt.accept(new StmtVarToArrayItemVisitor<>(), lookup);
	}
}
