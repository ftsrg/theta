package hu.bme.mit.inf.ttmc.program.cfa;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.common.Tuple4;
import hu.bme.mit.inf.ttmc.common.Tuples;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.cfa.impl.CFAImpl;
import hu.bme.mit.inf.ttmc.program.factory.ProgramFactory;
import hu.bme.mit.inf.ttmc.program.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.program.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.program.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.program.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.program.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.program.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.program.stmt.IfElseStmt;
import hu.bme.mit.inf.ttmc.program.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.program.stmt.ReturnStmt;
import hu.bme.mit.inf.ttmc.program.stmt.SkipStmt;
import hu.bme.mit.inf.ttmc.program.stmt.Stmt;
import hu.bme.mit.inf.ttmc.program.stmt.WhileStmt;
import hu.bme.mit.inf.ttmc.program.utils.StmtVisitor;

public class CFACreator {

	public static CFA create(final ExprFactory ef, final ProgramFactory pf, final List<Stmt> stmts) {
		final CFAImpl cfa = new CFAImpl();
		final CFACreatorVisitor visitor = new CFACreatorVisitor(ef, pf, cfa);
		createEdges(visitor, cfa, cfa.getInitLoc(), cfa.getFinalLoc(), ImmutableList.of(), ImmutableList.copyOf(stmts));
		return cfa;
	}

	//////

	private static void createEdges(final CFACreatorVisitor visitor, final CFAImpl cfa, final CFALoc source,
			final CFALoc target, final List<Stmt> prefix, final List<Stmt> postfix) {

		if (postfix.isEmpty()) {
			cfa.createEdge(source, target, prefix);
			return;
		} else {
			final Stmt stmt = postfix.get(0);
			final List<Stmt> newPostfix = postfix.subList(1, postfix.size());

			stmt.accept(visitor, Tuples.of(source, target, prefix, newPostfix));
		}

	}

	private static class CFACreatorVisitor
			implements StmtVisitor<Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>>, Void> {

		private final ExprFactory ef;
		private final ProgramFactory pf;
		private final CFAImpl cfa;

		private CFACreatorVisitor(final ExprFactory ef, final ProgramFactory pf, final CFAImpl cfa) {
			this.cfa = cfa;
			this.ef = ef;
			this.pf = pf;
		}

		private Void visitDefault(Stmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final List<Stmt> newPrefix = ImmutableList.<Stmt> builder().addAll(prefix).add(stmt).build();
			CFACreator.createEdges(this, cfa, source, target, newPrefix, postfix);

			return null;
		}

		@Override
		public Void visit(AssertStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final Stmt assumeNot = pf.Assume(ef.Not(stmt.getCond()));
			final List<Stmt> newPrefix1 = ImmutableList.<Stmt> builder().addAll(prefix).add(assumeNot).build();
			cfa.createEdge(source, cfa.getErrorLoc(), newPrefix1);

			final Stmt assume = pf.Assume(stmt.getCond());
			final List<Stmt> newPrefix2 = ImmutableList.<Stmt> builder().addAll(prefix).add(assume).build();
			CFACreator.createEdges(this, cfa, source, target, newPrefix2, postfix);

			return null;
		}

		@Override
		public <LhsType extends Type, RhsType extends LhsType> Void visit(AssignStmt<LhsType, RhsType> stmt,
				Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			return visitDefault(stmt, param);
		}

		@Override
		public Void visit(AssumeStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			return visitDefault(stmt, param);
		}

		@Override
		public Void visit(BlockStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			List<Stmt> newPostfix = ImmutableList.<Stmt> builder().addAll(stmt.getStmts()).addAll(postfix).build();
			createEdges(this, cfa, source, target, prefix, newPostfix);

			return null;
		}
		
		@Override
		public <ReturnType extends Type> Void visit(ReturnStmt<ReturnType> stmt,
				Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
//			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
//			final List<Stmt> postfix = param._4();
			
			List<Stmt> newPrefix = ImmutableList.<Stmt> builder().addAll(prefix).add(stmt).build();
			cfa.createEdge(source, cfa.getFinalLoc(), newPrefix);
			
			return null;
		}

		@Override
		public Void visit(DoStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final CFALoc loop = cfa.createLoc();
			final List<Stmt> entryPostfix = ImmutableList.of(stmt.getDo());
			createEdges(this, cfa, source, loop, prefix, entryPostfix);

			final Stmt assume = pf.Assume(stmt.getCond());
			final List<Stmt> loopPrefix = ImmutableList.of(assume);
			final List<Stmt> loopPostfix = ImmutableList.of(stmt.getDo());
			createEdges(this, cfa, loop, loop, loopPrefix, loopPostfix);

			final Stmt assumeNot = pf.Assume(ef.Not(stmt.getCond()));
			final List<Stmt> newPrefix = ImmutableList.of(assumeNot);
			createEdges(this, cfa, loop, target, newPrefix, postfix);

			return null;
		}

		@Override
		public <LhsType extends Type> Void visit(HavocStmt<LhsType> stmt,
				Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			return visitDefault(stmt, param);
		}

		@Override
		public Void visit(IfElseStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final Stmt assume = pf.Assume(stmt.getCond());
			final List<Stmt> thenPrefix = ImmutableList.<Stmt> builder().addAll(prefix).add(assume).build();
			final List<Stmt> thenPostfix = ImmutableList.<Stmt> builder().add(stmt.getThen()).addAll(postfix).build();
			createEdges(this, cfa, source, target, thenPrefix, thenPostfix);

			final Stmt assumeNot = pf.Assume(ef.Not(stmt.getCond()));
			final List<Stmt> elsePrefix = ImmutableList.<Stmt> builder().addAll(prefix).add(assumeNot).build();
			final List<Stmt> elsePostfix = ImmutableList.<Stmt> builder().add(stmt.getElse()).addAll(postfix).build();
			createEdges(this, cfa, source, target, elsePrefix, elsePostfix);

			return null;
		}

		@Override
		public Void visit(IfStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final Stmt assume = pf.Assume(stmt.getCond());
			final List<Stmt> thenPrefix = ImmutableList.<Stmt> builder().addAll(prefix).add(assume).build();
			final List<Stmt> thenPostfix = ImmutableList.<Stmt> builder().add(stmt.getThen()).addAll(postfix).build();
			createEdges(this, cfa, source, target, thenPrefix, thenPostfix);

			final Stmt assumeNot = pf.Assume(ef.Not(stmt.getCond()));
			final List<Stmt> elsePrefix = ImmutableList.<Stmt> builder().addAll(prefix).add(assumeNot).build();
			createEdges(this, cfa, source, target, elsePrefix, postfix);

			return null;
		}

		@Override
		public Void visit(SkipStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			createEdges(this, cfa, source, target, prefix, postfix);

			return null;
		}

		@Override
		public Void visit(WhileStmt stmt, Tuple4<CFALoc, CFALoc, List<Stmt>, List<Stmt>> param) {
			final CFALoc source = param._1();
			final CFALoc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final CFALoc loop = cfa.createLoc();
			cfa.createEdge(source, loop, prefix);

			final Stmt assume = pf.Assume(stmt.getCond());
			final List<Stmt> loopPrefix = ImmutableList.of(assume);
			final List<Stmt> loopPostfix = ImmutableList.of(stmt.getDo());
			createEdges(this, cfa, loop, loop, loopPrefix, loopPostfix);

			final Stmt assumeNot = pf.Assume(ef.Not(stmt.getCond()));
			final List<Stmt> newPrefix = ImmutableList.of(assumeNot);
			createEdges(this, cfa, loop, target, newPrefix, postfix);

			return null;
		}
	}
}
