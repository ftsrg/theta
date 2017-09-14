/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.formalism.cfa.creator;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.product.Product4;
import hu.bme.mit.theta.common.product.Tuple;
import hu.bme.mit.theta.core.stmt.AssertStmt;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.BlockStmt;
import hu.bme.mit.theta.core.stmt.DeclStmt;
import hu.bme.mit.theta.core.stmt.DoStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfElseStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.ReturnStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.WhileStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Builder;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

final class LbeCreator {

	static CFA create(final Stmt stmt) {
		final Builder cfaBuilder = CFA.builder();
		cfaBuilder.setInitLoc(cfaBuilder.createLoc("init"));
		cfaBuilder.setFinalLoc(cfaBuilder.createLoc("end"));
		cfaBuilder.setErrorLoc(cfaBuilder.createLoc("error"));
		final LBECreatorVisitor visitor = new LBECreatorVisitor(cfaBuilder);
		stmt.accept(visitor,
				Tuple.of(cfaBuilder.getInitLoc(), cfaBuilder.getFinalLoc(), new LinkedList<>(), new LinkedList<>()));
		return cfaBuilder.build();
	}

	private static class LBECreatorVisitor implements StmtVisitor<Product4<Loc, Loc, List<Stmt>, List<Stmt>>, Void> {

		private final CFA.Builder cfaBuilder;
		private int nextIndex;

		private LBECreatorVisitor(final CFA.Builder cfaBuilder) {
			this.cfaBuilder = cfaBuilder;
			nextIndex = 0;
		}

		////

		private void createEdges(final Loc source, final Loc target, final List<Stmt> prefix,
				final List<Stmt> postfix) {

			if (postfix.isEmpty()) {
				cfaBuilder.createEdge(source, target, prefix);
			} else {
				final Stmt head = postfix.get(0);
				final List<Stmt> tail = postfix.subList(1, postfix.size());
				head.accept(this, Tuple.of(source, target, prefix, tail));
			}
		}

		private Void visitSimpleStatement(final Stmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final List<Stmt> newPrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(stmt).build();
			final List<Stmt> newPostfix = postfix;

			createEdges(source, target, newPrefix, newPostfix);
			return null;
		}

		////

		@Override
		public Void visit(final SkipStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			createEdges(source, target, prefix, postfix);
			return null;
		}

		@Override
		public <DeclType extends Type> Void visit(final DeclStmt<DeclType> stmt,
				final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final List<Stmt> newPrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(initStmt(stmt)).build();
			final List<Stmt> newPostfix = postfix;
			createEdges(source, target, newPrefix, newPostfix);

			return null;
		}

		private <DeclType extends Type> Stmt initStmt(final DeclStmt<DeclType> stmt) {
			if (stmt.getInitVal().isPresent()) {
				return Assign(stmt.getVarDecl(), stmt.getInitVal().get());
			} else {
				return Havoc(stmt.getVarDecl());
			}
		}

		@Override
		public Void visit(final AssumeStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			return visitSimpleStatement(stmt, param);
		}

		@Override
		public Void visit(final AssertStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final Stmt assumeCorrect = Assume(stmt.getCond());
			final List<Stmt> correctPrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(assumeCorrect).build();
			final List<Stmt> correctPostfix = postfix;
			createEdges(source, target, correctPrefix, correctPostfix);

			final Stmt assumeError = Assume(Not(stmt.getCond()));
			final List<Stmt> errorPrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(assumeError).build();
			final List<Stmt> errorPostfix = ImmutableList.of();
			createEdges(source, cfaBuilder.getErrorLoc(), errorPrefix, errorPostfix);

			return null;
		}

		@Override
		public <DeclType extends Type> Void visit(final AssignStmt<DeclType> stmt,
				final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			return visitSimpleStatement(stmt, param);
		}

		@Override
		public <DeclType extends Type> Void visit(final HavocStmt<DeclType> stmt,
				final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			return visitSimpleStatement(stmt, param);
		}

		@Override
		public Void visit(final BlockStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final List<Stmt> newPrefix = prefix;
			final List<Stmt> newPostfix = ImmutableList.<Stmt>builder().addAll(stmt.getStmts()).addAll(postfix).build();
			createEdges(source, target, newPrefix, newPostfix);

			return null;
		}

		@Override
		public <ReturnType extends Type> Void visit(final ReturnStmt<ReturnType> stmt,
				final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final List<Stmt> prefix = param._3();

			final List<Stmt> newPrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(stmt).build();
			final List<Stmt> newPostfix = ImmutableList.of();
			createEdges(source, cfaBuilder.getFinalLoc(), newPrefix, newPostfix);

			return null;
		}

		@Override
		public Void visit(final IfStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final Stmt assumeThen = Assume(stmt.getCond());
			final List<Stmt> thenPrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(assumeThen).build();
			final List<Stmt> thenPostfix = ImmutableList.<Stmt>builder().add(stmt.getThen()).addAll(postfix).build();
			createEdges(source, target, thenPrefix, thenPostfix);

			final Stmt assumeElse = Assume(Not(stmt.getCond()));
			final List<Stmt> elsePrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(assumeElse).build();
			final List<Stmt> elsePostfix = postfix;
			createEdges(source, target, elsePrefix, elsePostfix);

			return null;
		}

		@Override
		public Void visit(final IfElseStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final Stmt assumeThen = Assume(stmt.getCond());
			final List<Stmt> thenPrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(assumeThen).build();
			final List<Stmt> thenPostfix = ImmutableList.<Stmt>builder().add(stmt.getThen()).addAll(postfix).build();
			createEdges(source, target, thenPrefix, thenPostfix);

			final Stmt assumeElse = Assume(Not(stmt.getCond()));
			final List<Stmt> elsePrefix = ImmutableList.<Stmt>builder().addAll(prefix).add(assumeElse).build();
			final List<Stmt> elsePostfix = ImmutableList.<Stmt>builder().add(stmt.getElse()).addAll(postfix).build();
			createEdges(source, target, elsePrefix, elsePostfix);

			return null;
		}

		@Override
		public Void visit(final WhileStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			Loc doLoc;
			if (prefix.isEmpty()) {
				doLoc = source;
			} else {
				doLoc = cfaBuilder.createLoc("L" + nextIndex++);
				final List<Stmt> entryPrefix = prefix;
				final List<Stmt> entryPostfix = Collections.emptyList();
				createEdges(source, doLoc, entryPrefix, entryPostfix);
			}

			final List<Stmt> loopPrefix = Collections.singletonList(Assume(stmt.getCond()));
			final List<Stmt> loopPostfix = Collections.singletonList(stmt.getDo());
			createEdges(doLoc, doLoc, loopPrefix, loopPostfix);

			final List<Stmt> exitPrefix = Collections.singletonList(Assume(Not(stmt.getCond())));
			final List<Stmt> exitPostfix = postfix;
			createEdges(doLoc, target, exitPrefix, exitPostfix);

			return null;
		}

		@Override
		public Void visit(final DoStmt stmt, final Product4<Loc, Loc, List<Stmt>, List<Stmt>> param) {
			final Loc source = param._1();
			final Loc target = param._2();
			final List<Stmt> prefix = param._3();
			final List<Stmt> postfix = param._4();

			final Loc doLoc = cfaBuilder.createLoc("L" + nextIndex++);

			final List<Stmt> entryPrefix = prefix;
			final List<Stmt> entryPostfix = ImmutableList.of(stmt.getDo());
			createEdges(source, doLoc, entryPrefix, entryPostfix);

			final List<Stmt> loopPrefix = Collections.singletonList(Assume(stmt.getCond()));
			final List<Stmt> loopPostfix = Collections.singletonList(stmt.getDo());
			createEdges(doLoc, doLoc, loopPrefix, loopPostfix);

			final List<Stmt> exitPrefix = Collections.singletonList(Assume(Not(stmt.getCond())));
			final List<Stmt> exitPostfix = postfix;
			createEdges(doLoc, target, exitPrefix, exitPostfix);

			return null;
		}

	}

}
