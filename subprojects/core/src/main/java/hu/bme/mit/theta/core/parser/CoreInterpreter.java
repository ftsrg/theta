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
package hu.bme.mit.theta.core.parser;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ref;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.math.BigInteger;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.UnaryOperator;

import com.google.common.primitives.Ints;

import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.parser.SExpr;
import hu.bme.mit.theta.common.parser.SExpr.SAtom;
import hu.bme.mit.theta.common.parser.SExpr.SList;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.GtExpr;
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public class CoreInterpreter {

	private final Env env;

	public CoreInterpreter(final Env env) {
		this.env = checkNotNull(env);
	}

	public void defineCommonTypes() {
		defineType("Bool", BoolType.getInstance());
		defineType("Int", IntType.getInstance());
		defineType("Rat", RatType.getInstance());
		defineType("Func", typeBinaryOperator(FuncType::of));
		defineType("Array", typeBinaryOperator(ArrayType::of));
	}

	public void defineCommonExprs() {
		defineExpr("true", TrueExpr.getInstance());
		defineExpr("false", FalseExpr.getInstance());
		defineExpr("not", exprUnaryOperator(NotExpr::create));
		defineExpr("and", exprMultiaryOperator(AndExpr::create));
		defineExpr("or", exprMultiaryOperator(OrExpr::create));
		defineExpr("=>", exprBinaryOperator(ImplyExpr::create));
		defineExpr("iff", exprBinaryOperator(IffExpr::create));
		defineExpr("xor", exprBinaryOperator(XorExpr::create));
		defineExpr("forall", exprQuantifier(ForallExpr::create));
		defineExpr("exists", exprQuantifier(ExistsExpr::create));
		defineExpr("ite", exprTernaryOperator(IteExpr::create));
		defineExpr("read", exprBinaryOperator(ArrayReadExpr::create));
		defineExpr("write", exprTernaryOperator(ArrayWriteExpr::create));
		defineExpr("mod", exprBinaryOperator(IntModExpr::create));
		defineExpr("rem", exprBinaryOperator(IntRemExpr::create));
		defineExpr("+", exprMultiaryOperator(AddExpr::create2));
		defineExpr("-", exprBinaryOperator(SubExpr::create2));
		defineExpr("*", exprMultiaryOperator(MulExpr::create2));
		defineExpr("/", exprBinaryOperator(DivExpr::create2));
		defineExpr("<", exprBinaryOperator(LtExpr::create2));
		defineExpr("<=", exprBinaryOperator(LeqExpr::create2));
		defineExpr(">", exprBinaryOperator(GtExpr::create2));
		defineExpr(">=", exprBinaryOperator(GeqExpr::create2));
		defineExpr("=", exprBinaryOperator(EqExpr::create2));
		defineExpr("/=", exprBinaryOperator(NeqExpr::create2));
	}

	public void defineCommonStmts() {
		defineStmt("skip", SkipStmt.getInstance());
		defineStmt("assign", createAssign());
		defineStmt("assume", createAssume());
		defineStmt("havoc", createHavoc());
	}

	////

	public void declare(final Decl<?> decl) {
		final String name = decl.getName();
		final Type type = decl.getType();
		if (type instanceof FuncType) {
			defineExpr(name, exprApplication(decl));
		} else {
			env.define(name, decl);
		}
	}

	public void defineType(final String symbol, final Type type) {
		env.define(symbol, type);
	}

	public void defineType(final String symbol, final BiFunction<Env, List<SExpr>, Type> function) {
		final Function<List<SExpr>, Type> interpretation = sexprs -> function.apply(env, sexprs);
		env.define(symbol, interpretation);
	}

	public void defineExpr(final String symbol, final Expr<?> expr) {
		env.define(symbol, expr);
	}

	public void defineExpr(final String symbol, final BiFunction<Env, List<SExpr>, Expr<?>> function) {
		final Function<List<SExpr>, Expr<?>> interpretation = sexprs -> function.apply(env, sexprs);
		env.define(symbol, interpretation);
	}

	public void defineStmt(final String symbol, final Stmt stmt) {
		env.define(symbol, stmt);
	}

	public void defineStmt(final String symbol, final BiFunction<Env, List<SExpr>, Stmt> function) {
		final Function<List<SExpr>, Stmt> interpretation = sexprs -> function.apply(env, sexprs);
		env.define(symbol, interpretation);
	}

	////

	public Type type(final SExpr sexpr) {
		return (Type) eval(sexpr);
	}

	public Expr<?> expr(final SExpr sexpr) {
		final Object object = eval(sexpr);
		if (object instanceof Expr) {
			return (Expr<?>) object;
		} else if (object instanceof Decl) {
			return Ref((Decl<?>) object);
		} else if (object instanceof Integer) {
			return Int(BigInteger.valueOf((Integer) object));
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public Stmt stmt(final SExpr sexpr) {
		return (Stmt) eval(sexpr);
	}

	private VarDecl<?> var(final SExpr sexpr) {
		return (VarDecl<?>) eval(sexpr);
	}

	public void push() {
		env.push();
	}

	public void pop() {
		env.pop();
	}

	////

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

	////

	public final BiFunction<Env, List<SExpr>, Type> typeBinaryOperator(final BinaryOperator<Type> function) {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 2);
			final Type type1 = type(sexprs.get(0));
			final Type type2 = type(sexprs.get(1));
			return function.apply(type1, type2);
		};
	}

	public final BiFunction<Env, List<SExpr>, Expr<?>> exprUnaryOperator(final UnaryOperator<Expr<?>> function) {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 1);
			final Expr<?> op = expr(sexprs.get(0));
			return function.apply(op);
		};
	}

	public final BiFunction<Env, List<SExpr>, Expr<?>> exprBinaryOperator(final BinaryOperator<Expr<?>> function) {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 2);
			final Expr<?> op1 = expr(sexprs.get(0));
			final Expr<?> op2 = expr(sexprs.get(1));
			return function.apply(op1, op2);
		};
	}

	public final BiFunction<Env, List<SExpr>, Expr<?>> exprTernaryOperator(final TernaryOperator<Expr<?>> function) {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 3);
			final Expr<?> op1 = expr(sexprs.get(0));
			final Expr<?> op2 = expr(sexprs.get(1));
			final Expr<?> op3 = expr(sexprs.get(2));
			return function.apply(op1, op2, op3);
		};
	}

	public final BiFunction<Env, List<SExpr>, Expr<?>> exprMultiaryOperator(
			final Function<List<Expr<?>>, Expr<?>> function) {
		return (env, sexprs) -> {
			return function.apply(sexprs.stream().map(this::expr).collect(toImmutableList()));
		};
	}

	public final BiFunction<Env, List<SExpr>, Expr<?>> exprQuantifier(
			final BiFunction<List<ParamDecl<?>>, Expr<?>, Expr<?>> function) {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 2);
			env.push();
			final List<ParamDecl<?>> paramDecls = createParams(sexprs.get(0));
			paramDecls.forEach(this::declare);
			final Expr<?> op = expr(sexprs.get(1));
			env.pop();
			return function.apply(paramDecls, op);
		};
	}

	public final BiFunction<Env, List<SExpr>, Expr<?>> exprApplication(final Decl<?> decl) {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 1);
			final Expr<?> func = decl.getRef();
			final Expr<?> param = expr(sexprs.get(0));
			return FuncAppExpr.create(func, param);
		};
	}

	private List<ParamDecl<?>> createParams(final SExpr sexpr) {
		checkArgument(sexpr.isList());
		final List<SExpr> sexprs = sexpr.asList().getList();
		return sexprs.stream().map(this::createParam).collect(toImmutableList());
	}

	private ParamDecl<?> createParam(final SExpr sexpr) {
		checkArgument(sexpr.isList());
		final List<SExpr> sexprs = sexpr.asList().getList();
		checkArgument(sexprs.size() == 2);
		final SExpr sexpr1 = sexprs.get(0);
		final SExpr sexpr2 = sexprs.get(1);
		checkArgument(sexpr1.isAtom());
		final String name = sexpr1.asAtom().getAtom();
		final Type type = type(sexpr2);
		return Param(name, type);
	}

	private BiFunction<Env, List<SExpr>, Stmt> createAssign() {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 2);
			final VarDecl<?> varDecl = var(sexprs.get(0));
			final Expr<?> expr = expr(sexprs.get(1));
			return AssignStmt.create(varDecl, expr);
		};
	}

	private BiFunction<Env, List<SExpr>, Stmt> createAssume() {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 1);
			final Expr<?> expr = expr(sexprs.get(0));
			return AssumeStmt.create(expr);
		};
	}

	private BiFunction<Env, List<SExpr>, Stmt> createHavoc() {
		return (env, sexprs) -> {
			checkArgument(sexprs.size() == 1);
			final VarDecl<?> varDecl = var(sexprs.get(0));
			return HavocStmt.of(varDecl);
		};
	}

}
