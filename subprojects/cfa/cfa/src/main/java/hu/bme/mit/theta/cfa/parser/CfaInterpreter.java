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
package hu.bme.mit.theta.cfa.parser;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.core.decl.Decls.Var;

import java.util.List;
import java.util.function.Function;

import com.google.common.primitives.Ints;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Edge;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.common.parser.SExpr;
import hu.bme.mit.theta.common.parser.SExpr.SAtom;
import hu.bme.mit.theta.common.parser.SExpr.SList;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.parser.CoreInterpreter;
import hu.bme.mit.theta.core.parser.Env;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;

final class CfaInterpreter {

	private final Env env;
	private final CoreInterpreter interpreter;

	public CfaInterpreter(final Env env) {
		this.env = checkNotNull(env);
		this.interpreter = new CoreInterpreter(env);
		initEnv();
	}

	private void initEnv() {
		interpreter.defineCommonTypes();
		interpreter.defineCommonExprs();
		interpreter.defineCommonStmts();
		env.define("process", cfaCreator());
		env.define("var", varCreator());
		env.define("loc", locCreator(LocKind.LOC));
		env.define("init", locCreator(LocKind.INIT));
		env.define("final", locCreator(LocKind.FINAL));
		env.define("error", locCreator(LocKind.ERROR));
		env.define("edge", edgeCreator());
	}

	public CFA cfa(final SExpr sexpr) {
		return (CFA) eval(sexpr);
	}

	public Loc loc(final SExpr sexpr) {
		return (Loc) eval(sexpr);
	}

	private Object eval(final SExpr sexpr) {
		if (sexpr.isAtom()) {
			return evalAtom(sexpr.asAtom());
		} else if (sexpr.isList()) {
			return evalList(sexpr.asList());
		} else {
			throw new AssertionError();
		}
	}

	private Object evalAtom(final SAtom satom) {
		final String symbol = satom.getAtom();
		final Integer integer = Ints.tryParse(symbol);
		if (integer != null) {
			return integer;
		} else {
			final Object value = env.eval(symbol);
			return value;
		}
	}

	private Object evalList(final SList slist) {
		final List<SExpr> list = slist.getList();
		final SExpr head = head(list);
		final List<SExpr> tail = tail(list);
		if (head.isAtom()) {
			final String symbol = head.asAtom().getAtom();
			final Object object = env.eval(symbol);
			@SuppressWarnings("unchecked") final Function<List<SExpr>, ?> interpretation = (Function<List<SExpr>, ?>) object;
			final Object value = interpretation.apply(tail);
			return value;
		} else if (head.isList()) {
			throw new UnsupportedOperationException();
		} else {
			throw new AssertionError();
		}
	}

	private Function<List<SExpr>, CFA> cfaCreator() {
		return sexprs -> {
			final CFA.Builder builder = CFA.builder();
			env.push();
			for (final SExpr sexpr : sexprs) {
				final Object object = eval(sexpr);
				if (object instanceof VarDecl) {
					final VarDecl<?> varDecl = (VarDecl<?>) object;
					env.define(varDecl.getName(), varDecl);
				} else if (object instanceof LocContext) {
					final Loc loc = createLoc(builder, (LocContext) object);
					env.define(loc.getName(), loc);
				} else if (object instanceof EdgeContext) {
					createEdge(builder, (EdgeContext) object);
				} else {
					throw new UnsupportedOperationException();
				}
			}
			env.pop();
			return builder.build();
		};
	}

	private Loc createLoc(final CFA.Builder builder, final LocContext context) {
		final Loc loc = builder.createLoc(context.name);
		switch (context.kind) {
			case LOC:
				break;
			case INIT:
				builder.setInitLoc(loc);
				break;
			case FINAL:
				builder.setFinalLoc(loc);
				break;
			case ERROR:
				builder.setErrorLoc(loc);
				break;
			default:
				throw new AssertionError();
		}
		return loc;
	}

	private Edge createEdge(final CFA.Builder builder, final EdgeContext context) {
		final Edge edge = builder.createEdge(context.source, context.target, context.stmt);
		return edge;

	}

	private Function<List<SExpr>, VarDecl<?>> varCreator() {
		return sexprs -> {
			checkArgument(sexprs.size() == 2);
			final String name = sexprs.get(0).asAtom().getAtom();
			final Type type = interpreter.type(sexprs.get(1));
			final VarDecl<?> varDecl = Var(name, type);
			return varDecl;
		};
	}

	private Function<List<SExpr>, LocContext> locCreator(final LocKind kind) {
		return sexprs -> {
			checkArgument(sexprs.size() == 1);
			final String name = sexprs.get(0).asAtom().getAtom();
			return new LocContext(kind, name);
		};
	}

	private Function<List<SExpr>, EdgeContext> edgeCreator() {
		return sexprs -> {
			checkArgument(sexprs.size() == 3);
			final Loc source = loc(sexprs.get(0));
			final Loc target = loc(sexprs.get(1));
			final Stmt stmt = interpreter.stmt(sexprs.get(2));
			return new EdgeContext(source, target, stmt);
		};
	}

	////

	private static final class LocContext {
		private final LocKind kind;
		private final String name;

		private LocContext(final LocKind kind, final String name) {
			this.kind = checkNotNull(kind);
			this.name = checkNotNull(name);
		}
	}

	private enum LocKind {
		LOC, INIT, FINAL, ERROR
	}

	private static final class EdgeContext {
		private final Loc source;
		private final Loc target;
		private final Stmt stmt;

		private EdgeContext(final Loc source, final Loc target, final Stmt stmt) {
			this.source = checkNotNull(source);
			this.target = checkNotNull(target);
			this.stmt = checkNotNull(stmt);
		}
	}
}
