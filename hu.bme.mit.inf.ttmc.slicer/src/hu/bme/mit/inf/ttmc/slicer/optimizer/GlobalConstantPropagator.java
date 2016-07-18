package hu.bme.mit.inf.ttmc.slicer.optimizer;

import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assert;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assign;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Return;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.ReturnStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.slicer.cfg.BranchStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.SequentialStmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.dependence.UseDefineChain;

public class GlobalConstantPropagator implements CFGOptimizer {

	@SuppressWarnings("unchecked")
	@Override
	public CFG transform(CFG input) {
		CFG cfg = input.copy();
		UseDefineChain ud = new UseDefineChain(cfg);

		List<StmtCFGNode> nodes = cfg.nodes().stream()
			.filter(s -> s instanceof StmtCFGNode)
			.map(s -> (StmtCFGNode) s)
			.collect(Collectors.toList());


		for (StmtCFGNode node : nodes) {
			// For each used variable
			Map<VarDecl<? extends Type>, LitExpr<? extends Type>> map = new HashMap<>();
			ud.usedVariables(node).forEach(var -> {
				List<StmtCFGNode> defs = ud.varDefinitionNodes(node, var);
				if (defs.size() != 1)
					return;

				StmtCFGNode defNode = defs.get(0);
				Stmt defStmt = defs.get(0).getStmt();
				// We need the definition to be constant
				if (defStmt instanceof AssignStmt<?, ?>) {
					AssignStmt<? extends Type, ? extends Type> assign = (AssignStmt<? extends Type, ? extends Type>) defStmt;
					if (assign.getExpr() instanceof LitExpr<?>) {
						// It's a constant, we can replace it
						map.put(assign.getVarDecl(), (LitExpr<? extends Type>) assign.getExpr());
					}
				}
			});

			ConstantFolderExprVisitor visitor = new ConstantFolderExprVisitor(map);
			this.processNode(node, visitor);
		}

		return cfg;
	}

	private void processNode(StmtCFGNode node, ConstantFolderExprVisitor visitor) {
		// TODO: This is uglier than the east end of a horse heading west
		Stmt s = node.getStmt();
		if (s instanceof AssignStmt<?, ?>) {
			AssignStmt<? extends Type, ? extends Type> assign = (AssignStmt<? extends Type, ? extends Type>) s;
			Expr<? extends Type> expr = assign.getExpr().accept(visitor, null);

			if (expr != assign.getExpr()) {
				 StmtCFGNode newNode = new SequentialStmtCFGNode(
					Assign(assign.getVarDecl(), ExprUtils.cast(expr, assign.getVarDecl().getType().getClass()))
				 );

				 node.replace(newNode);
			}
		} else if (s instanceof AssumeStmt) {
			AssumeStmt assume = (AssumeStmt) s;
			Expr<? extends BoolType> cond = ExprUtils.cast(assume.getCond().accept(visitor, null), BoolType.class);

			BranchStmtCFGNode newNode = new BranchStmtCFGNode(Assume(cond));
			node.replace(newNode);
		} else if (s instanceof ReturnStmt<?>) {
			ReturnStmt<? extends Type> ret = (ReturnStmt<? extends Type>) s;
			Expr<? extends Type> expr = ret.getExpr().accept(visitor, null);

			StmtCFGNode newNode = new SequentialStmtCFGNode(Return(expr));
			node.replace(newNode);
		} else if (s instanceof AssertStmt) {
			AssertStmt assertStmt = (AssertStmt) s;
			Expr<? extends BoolType> cond = ExprUtils.cast(assertStmt.getCond().accept(visitor, null), BoolType.class);

			StmtCFGNode newNode = new SequentialStmtCFGNode(Assert(cond));
			node.replace(newNode);
		} else if (s instanceof HavocStmt<?>){
			// Do nothing...
		} else {
			throw new UnsupportedOperationException();
		}
	}

}
