package hu.bme.mit.inf.ttmc.formalism.utils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.common.Tuple2;
import hu.bme.mit.inf.ttmc.common.Tuples;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.IndexMap;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.VarMap;

public class StmtUnroller {

	private final VarMap varMap;
	private final StmtToExprVisitor visitor;

	public StmtUnroller(final ExprFactory ef, final DeclFactory df) {
		varMap = new VarMap(df);
		visitor = new StmtToExprVisitor(ef);
	}

	public Collection<Expr<? extends BoolType>> pathExprs(Stmt... stmts) {
		return pathExprs(Arrays.asList(stmts));
	}

	public Collection<Expr<? extends BoolType>> pathExprs(final List<Stmt> stmts) {
		final List<Expr<? extends BoolType>> result = new ArrayList<>();
		final IndexMap indexMap = new IndexMap();

		for (Stmt stmt : stmts) {
			final Expr<? extends BoolType> expr = pathExpr(stmt, indexMap);
			if (expr != null) {
				result.add(expr);
			}
		}

		return result;
	}

	private Expr<? extends BoolType> pathExpr(Stmt stmt, IndexMap indexMap) {
		return stmt.accept(visitor, Tuples.of(varMap, indexMap));
	}

	////

	private static class StmtToExprVisitor extends FailStmtVisitor<Tuple2<VarMap, IndexMap>, Expr<? extends BoolType>> {

		private final ExprFactory ef;
		private final VarToConstVisitor visitor;

		private StmtToExprVisitor(final ExprFactory ef) {
			this.ef = ef;
			visitor = new VarToConstVisitor();
		}

		////////

		@Override
		public Expr<? extends BoolType> visit(AssumeStmt stmt, Tuple2<VarMap, IndexMap> param) {
			final VarMap varMap = param._1();
			final IndexMap indexMap = param._2();

			final Expr<? extends BoolType> cond = stmt.getCond();
			final Expr<?> expr = cond.accept(visitor, Tuples.of(varMap, indexMap));
			@SuppressWarnings("unchecked")
			final Expr<? extends BoolType> result = (Expr<? extends BoolType>) expr;

			return result;
		}

		@Override
		public <DeclType extends Type, ExprType extends DeclType> Expr<? extends BoolType> visit(
				AssignStmt<DeclType, ExprType> stmt, Tuple2<VarMap, IndexMap> param) {

			final VarMap varMap = param._1();
			final IndexMap indexMap = param._2();

			final Expr<?> expr = stmt.getExpr();
			final Expr<?> rhs = expr.accept(visitor, Tuples.of(varMap, indexMap));
			
			final VarDecl<?> varDecl = stmt.getVarDecl();
			// side effect on indexMap
			indexMap.inc(varDecl);
			final int index = indexMap.getIndex(varDecl);
			final ConstDecl<?> constDecl = varMap.getConstDecl(varDecl, index);
			final Expr<?> lhs = constDecl.getRef();
			
			final Expr<? extends BoolType> result = ef.Eq(lhs, rhs);
			return result;
		}

		@Override
		public <DeclType extends Type> Expr<? extends BoolType> visit(HavocStmt<DeclType> stmt,
				Tuple2<VarMap, IndexMap> param) {
//			final VarMap varMap = param._1();
			final IndexMap indexMap = param._2();

			final VarDecl<?> varDecl = stmt.getVarDecl();
			// side effect on indexMap
			indexMap.inc(varDecl);

			return null;
		}

		////////

		private static class VarToConstVisitor extends ExprRewriterVisitor<Tuple2<VarMap, IndexMap>>
				implements ProgExprVisitor<Tuple2<VarMap, IndexMap>, Expr<?>> {

			@Override
			public <ExprType extends Type> Expr<ExprType> visit(PrimedExpr<ExprType> expr,
					Tuple2<VarMap, IndexMap> param) {
				throw new UnsupportedOperationException();
			}

			@Override
			public <DeclType extends Type> ConstRefExpr<DeclType> visit(VarRefExpr<DeclType> expr,
					Tuple2<VarMap, IndexMap> param) {
				final VarMap varMap = param._1();
				final IndexMap indexMap = param._2();

				final VarDecl<DeclType> varDecl = expr.getDecl();
				final int index = indexMap.getIndex(varDecl);

				final ConstDecl<DeclType> constDecl = varMap.getConstDecl(varDecl, index);
				final ConstRefExpr<DeclType> constRef = constDecl.getRef();

				return constRef;
			}

			@Override
			public <ReturnType extends Type> Expr<?> visit(ProcRefExpr<ReturnType> expr,
					Tuple2<VarMap, IndexMap> param) {
				throw new UnsupportedOperationException();
			}

			@Override
			public <ReturnType extends Type> Expr<?> visit(ProcCallExpr<ReturnType> expr,
					Tuple2<VarMap, IndexMap> param) {
				throw new UnsupportedOperationException();
			}
		}
	}

}
