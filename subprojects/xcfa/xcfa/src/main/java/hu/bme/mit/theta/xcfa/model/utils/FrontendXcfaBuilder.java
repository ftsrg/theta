package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Dereference;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssignment;
import hu.bme.mit.theta.frontend.transformation.model.statements.CAssume;
import hu.bme.mit.theta.frontend.transformation.model.statements.CBreak;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCase;
import hu.bme.mit.theta.frontend.transformation.model.statements.CCompound;
import hu.bme.mit.theta.frontend.transformation.model.statements.CContinue;
import hu.bme.mit.theta.frontend.transformation.model.statements.CDefault;
import hu.bme.mit.theta.frontend.transformation.model.statements.CDoWhile;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CFor;
import hu.bme.mit.theta.frontend.transformation.model.statements.CFunction;
import hu.bme.mit.theta.frontend.transformation.model.statements.CGoto;
import hu.bme.mit.theta.frontend.transformation.model.statements.CIf;
import hu.bme.mit.theta.frontend.transformation.model.statements.CInitializerList;
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram;
import hu.bme.mit.theta.frontend.transformation.model.statements.CRet;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatementVisitorBase;
import hu.bme.mit.theta.frontend.transformation.model.statements.CSwitch;
import hu.bme.mit.theta.frontend.transformation.model.statements.CWhile;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.NamedType;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.ProcedureCall;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class FrontendXcfaBuilder extends CStatementVisitorBase<FrontendXcfaBuilder.ParamPack, XcfaLocation> {

	private final Map<String, XcfaLocation> locationLut = new LinkedHashMap<>();
	private XcfaLocation getLoc(final XcfaProcedure.Builder builder, final String name) {
		if(name == null) return getAnonymousLoc(builder);
		locationLut.putIfAbsent(name, XcfaLocation.create(name));
		XcfaLocation location = locationLut.get(name);
		builder.addLoc(location);
		return location;
	}
	private XcfaLocation getAnonymousLoc(final XcfaProcedure.Builder builder) {
		return getLoc(builder, "__loc_" + XcfaLocation.uniqeCounter());
	}

	protected <T> void propagateMetadata(CStatement source, T newOwner) {
		FrontendMetadata.create(newOwner, "sourceStatement", source);
	}


	public XCFA.Builder buildXcfa(CProgram cProgram) {
		XCFA.Builder builder = XCFA.builder();
		builder.setDynamic(true);

		List<XcfaLabel> initStmtList = new ArrayList<>();
		for (Tuple2<CDeclaration, VarDecl<?>> globalDeclaration : cProgram.getGlobalDeclarations()) {
			CComplexType type = CComplexType.getType(globalDeclaration.get2().getRef());
			if(type instanceof CVoid || type instanceof CStruct) {
				System.err.println("WARNING: Not handling init expression of " + globalDeclaration.get1() + " as it is non initializable");
				continue;
			}
			builder.addGlobalVar(globalDeclaration.get2(), type.getNullValue());
			if(globalDeclaration.get1().getInitExpr() != null) {
				initStmtList.add(Stmt(Assign(cast(globalDeclaration.get2(), globalDeclaration.get2().getType()), cast(type.castTo(globalDeclaration.get1().getInitExpr().getExpression()), globalDeclaration.get2().getType()))));
			} else {
				initStmtList.add(Stmt(Assign(cast(globalDeclaration.get2(), globalDeclaration.get2().getType()), cast(type.getNullValue(), globalDeclaration.get2().getType()))));
			}
		}
		XcfaProcess.Builder procBuilder = XcfaProcess.builder();
		for (CFunction function : cProgram.getFunctions()) {
			XcfaProcedure.Builder build = handleFunction(function, initStmtList);
			procBuilder.addProcedure(build);
			if(build.getName().equals("main")) procBuilder.setMainProcedure(build);
		}
		builder.addProcess(procBuilder);
		builder.setMainProcess(procBuilder);
		return builder;
	}

	private XcfaProcedure.Builder handleFunction(CFunction function, List<XcfaLabel> param) {
		locationLut.clear();
		List<VarDecl<?>> flatVariables = function.getFlatVariables();
		CDeclaration funcDecl = function.getFuncDecl();
		CStatement compound = function.getCompound();

		XcfaProcedure.Builder builder = XcfaProcedure.builder();
		for (VarDecl<?> flatVariable : flatVariables) {
			builder.createVar(flatVariable, null);
		}
		builder.setRetType(funcDecl.getActualType() instanceof CVoid ? null : funcDecl.getActualType().getSmtType());
		builder.setName(funcDecl.getName());
		if(!(funcDecl.getActualType() instanceof CVoid)) {
			VarDecl<?> var = Var(funcDecl.getName() + "_ret", funcDecl.getActualType().getSmtType());
			FrontendMetadata.create(var.getRef(), "cType", funcDecl.getActualType());
			builder.createParam(XcfaProcedure.Direction.OUT, var);
		} else {
			// TODO we assume later that there is always a ret var, but this should change
			VarDecl<?> var = Var(funcDecl.getName() + "_ret", funcDecl.getActualType().getSmtType());
			NamedType signedIntType = CSimpleTypeFactory.NamedType("int");
			signedIntType.setSigned(true);
			FrontendMetadata.create(var.getRef(), "cType", signedIntType);
			builder.createParam(XcfaProcedure.Direction.OUT, var);
		}

		for (CDeclaration functionParam : funcDecl.getFunctionParams()) {
			checkState(functionParam.getActualType() instanceof CVoid ||  functionParam.getVarDecls().size() > 0, "Function param should have an associated variable!");
			for (VarDecl<?> varDecl : functionParam.getVarDecls()) {
				if(varDecl != null) builder.createParam(XcfaProcedure.Direction.IN, varDecl);
			}
		}
		XcfaLocation init = getAnonymousLoc(builder);
		builder.addLoc(init);
		propagateMetadata(function, init);
		builder.setInitLoc(init);
		if(param.size() > 0 && builder.getName().equals("main")) {
			XcfaLocation endinit = getAnonymousLoc(builder);
			builder.addLoc(endinit);
			propagateMetadata(function, endinit);
			XcfaEdge edge = XcfaEdge.of(init, endinit, param);
			builder.addEdge(edge);
			propagateMetadata(function, edge);
			init = endinit;
		}
		XcfaLocation ret = getAnonymousLoc(builder);
		builder.addLoc(ret);
		propagateMetadata(function, ret);
		XcfaLocation end = compound.accept(this, new ParamPack(builder, init, null, null, ret));
		XcfaEdge edge = XcfaEdge.of(end, ret, List.of());
		builder.addEdge(edge);
		propagateMetadata(function, edge);
		builder.setFinalLoc(ret);
		return builder;
	}


	@Override
	public XcfaLocation visit(CAssignment statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		Expr<?> lValue = statement.getlValue();
		CStatement rValue = statement.getrValue();
		Map<Type, VarDecl<ArrayType<?, ?>>> memoryMaps = CAssignment.getMemoryMaps();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation location = getAnonymousLoc(builder);
		builder.addLoc(location);
		propagateMetadata(statement, location);
		initLoc = rValue.accept(this, new ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc));
		checkState(lValue instanceof Dereference || lValue instanceof ArrayReadExpr || lValue instanceof RefExpr && ((RefExpr<?>) lValue).getDecl() instanceof VarDecl<?>, "lValue must be a variable, pointer dereference or an array element!");
		Expr<?> rExpression = statement.getrExpression();
		if (lValue instanceof ArrayReadExpr) {
			Stack<Expr<?>> exprs = new Stack<>();
			Expr<?> expr = rExpression;
			VarDecl<?> var = createArrayWriteExpr((ArrayReadExpr<?, ? extends Type>) lValue, expr, exprs);
			xcfaEdge = XcfaEdge.of(initLoc, location, List.of(Stmt(Assign(cast(var, var.getType()), cast(exprs.pop(), var.getType())))));
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		} else if (lValue instanceof Dereference) {
			Expr<?> op = ((Dereference<?, ?>) lValue).getOp();
			Type type = op.getType();
			Type ptrType = CComplexType.getUnsignedLong().getSmtType();
			if(!memoryMaps.containsKey(type)) {
				VarDecl<ArrayType<?,?>> var = Var("memory_" + type.toString(), ArrayType.of(ptrType, type));
				memoryMaps.put(type, var);
				FrontendMetadata.create(var, "defaultElement", CComplexType.getType(op).getNullValue());
			}
			VarDecl<ArrayType<?, ?>> memoryMap = memoryMaps.get(type);
			FrontendMetadata.create(op, "dereferenced", true);
			FrontendMetadata.create(op, "refSubstitute", memoryMap);
			ArrayWriteExpr<Type, Type> write = Write(cast(memoryMap.getRef(), ArrayType.of(ptrType, type)),
					cast(((Dereference<?, ?>) lValue).getOp(), ptrType),
					cast(rExpression, type));
			FrontendMetadata.create(write, "cType", new CArray(null, CComplexType.getType(((Dereference<?, ?>) lValue).getOp())));
			xcfaEdge = XcfaEdge.of(initLoc, location, List.of(Stmt(Assign(cast(memoryMap, ArrayType.of(ptrType, type)), write))));
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		}
		else {
			xcfaEdge = XcfaEdge.of(initLoc, location, List.of(Stmt(Assign(cast((VarDecl<?>) ((RefExpr<?>) lValue).getDecl(), ((VarDecl<?>) ((RefExpr<?>) lValue).getDecl()).getType()), cast(rExpression, rExpression.getType())))));
			if(CComplexType.getType(lValue) instanceof CPointer && CComplexType.getType(rExpression) instanceof CPointer) {
				checkState(rExpression instanceof RefExpr || rExpression instanceof Reference);

				if(rExpression instanceof RefExpr) {
					Optional<Object> pointsTo = FrontendMetadata.getMetadataValue(lValue, "pointsTo");
					if(pointsTo.isPresent() && pointsTo.get() instanceof Collection) {
						((Collection<Expr<?>>) pointsTo.get()).add(rExpression);
					} else {
						pointsTo = Optional.of(new LinkedHashSet<Expr<?>>(Set.of(rExpression)));
					}
					FrontendMetadata.create(lValue, "pointsTo", pointsTo.get());
				}
				else {
					Optional<Object> pointsTo = FrontendMetadata.getMetadataValue(lValue, "pointsTo");
					if(pointsTo.isPresent() && pointsTo.get() instanceof Collection) {
						((Collection<Expr<?>>) pointsTo.get()).add(((Reference<?, ?>) rExpression).getOp());
					} else {
						pointsTo = Optional.of(new LinkedHashSet<Expr<?>>(Set.of(((Reference<?, ?>) rExpression).getOp())));
					}
					FrontendMetadata.create(lValue, "pointsTo", pointsTo.get());
				}
			}
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		}
		return location;
	}

	private <P extends Type, T extends Type> VarDecl<?> createArrayWriteExpr(ArrayReadExpr<P, T> lValue, Expr<?> rExpression, Stack<Expr<?>> exprs) {
		Expr<ArrayType<P, T>> array = lValue.getArray();
		Expr<P> index = lValue.getIndex();
		ArrayWriteExpr<P, T> arrayWriteExpr = ArrayWriteExpr.of(array, index, cast(rExpression, array.getType().getElemType()));
		FrontendMetadata.create(arrayWriteExpr, "cType", new CArray(null, CComplexType.getType(rExpression)));
		if (array instanceof RefExpr && ((RefExpr<ArrayType<P, T>>) array).getDecl() instanceof VarDecl) {
			exprs.push(arrayWriteExpr);
			return (VarDecl<?>) ((RefExpr<ArrayType<P, T>>) array).getDecl();
		} else if (array instanceof ArrayReadExpr) {
			return createArrayWriteExpr((ArrayReadExpr<P, ?>) array, arrayWriteExpr, exprs);
		} else throw new UnsupportedOperationException("Possible malformed array write?");
	}

	@Override
	public XcfaLocation visit(CAssume statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation location = getAnonymousLoc(builder);
		builder.addLoc(location);
		propagateMetadata(statement, location);

		xcfaEdge = XcfaEdge.of(initLoc, location, Collections.singletonList(Stmt(statement.getAssumeStmt())));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		return location;
	}

	@Override
	public XcfaLocation visit(CBreak statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge edge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		edge = XcfaEdge.of(initLoc, breakLoc, List.of());
		XcfaLocation unreachableLoc = XcfaLocation.create("Unreachable" + XcfaLocation.uniqeCounter());
		builder.addLoc(unreachableLoc);
		propagateMetadata(statement, unreachableLoc);
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		return unreachableLoc;
	}

	@Override
	public XcfaLocation visit(CCall statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		VarDecl<?> ret = statement.getRet();
		List<CStatement> myParams = statement.getParams();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation location = getAnonymousLoc(builder);
		builder.addLoc(location);
		propagateMetadata(statement, location);
		List<Expr<?>> params = new ArrayList<>();
		builder.createVar(ret, null);
		params.add(ret.getRef());
		for (CStatement cStatement : myParams) {
			initLoc = cStatement.accept(this, new ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc));
		}
		params.addAll(myParams.stream().map(CStatement::getExpression).collect(Collectors.toList()));
		final XcfaLabel.ProcedureCallXcfaLabel call = ProcedureCall(params, statement.getFunctionId());
		propagateMetadata(statement, call);
		xcfaEdge = XcfaEdge.of(initLoc, location, List.of(call));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		return location;
	}

	@Override
	public XcfaLocation visit(CCase statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		return statement.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
	}

	@Override
	public XcfaLocation visit(CCompound statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		CStatement preStatements = statement.getPreStatements();
		CStatement postStatements = statement.getPostStatements();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge edge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		lastLoc = initLoc;
		if(preStatements != null) lastLoc = preStatements.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		for (CStatement cStatement : statement.getcStatementList()) {
			if(cStatement != null) lastLoc = cStatement.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		}
		if(postStatements != null) lastLoc = postStatements.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		return lastLoc;	}

	@Override
	public XcfaLocation visit(CContinue statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge edge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		edge = XcfaEdge.of(initLoc, continueLoc, List.of());
		XcfaLocation unreachableLoc = XcfaLocation.create("Unreachable" + XcfaLocation.uniqeCounter());
		builder.addLoc(unreachableLoc);
		propagateMetadata(statement, unreachableLoc);
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		return unreachableLoc;
	}

	@Override
	public XcfaLocation visit(CDefault statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		return statement.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
	}

	@Override
	public XcfaLocation visit(CDoWhile statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;
		CStatement body = statement.getBody();
		CStatement guard = statement.getGuard();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		XcfaLocation endLoc = getAnonymousLoc(builder);
		XcfaLocation innerEndLoc = getAnonymousLoc(builder);
		XcfaLocation innerInnerGuard = getAnonymousLoc(builder);
		XcfaLocation outerInnerGuard = getAnonymousLoc(builder);
		builder.addLoc(endLoc);
		propagateMetadata(statement, endLoc);
		builder.addLoc(innerInnerGuard);
		propagateMetadata(statement, innerInnerGuard);
		builder.addLoc(outerInnerGuard);
		propagateMetadata(statement, outerInnerGuard);
		builder.addLoc(innerEndLoc);
		propagateMetadata(statement, innerEndLoc);
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation lastBody = body.accept(this, new ParamPack(builder, initLoc, endLoc, innerEndLoc, returnLoc));
		xcfaEdge = XcfaEdge.of(lastBody, innerEndLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation lastPre = buildWithoutPostStatement(guard, new ParamPack(builder, innerEndLoc, null, null, returnLoc));
		final AssumeStmt assume = Assume(Neq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
		propagateMetadata(guard, assume);
		xcfaEdge = XcfaEdge.of(lastPre, innerInnerGuard, List.of(Stmt(assume)));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		final AssumeStmt assume1 = Assume(Eq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
		propagateMetadata(guard, assume1);
		xcfaEdge = XcfaEdge.of(lastPre, outerInnerGuard, List.of(Stmt(assume1)));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation outerLastGuard = buildPostStatement(guard, new ParamPack(builder, outerInnerGuard, null, null, null));
		XcfaLocation innerLastGuard = buildPostStatement(guard, new ParamPack(builder, innerInnerGuard, null, null, null));
		xcfaEdge = XcfaEdge.of(outerLastGuard, endLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		xcfaEdge = XcfaEdge.of(innerLastGuard, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		return endLoc;
	}

	@Override
	public XcfaLocation visit(CExpr statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		return lastLoc;
	}

	@Override
	public XcfaLocation visit(CFor statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		CStatement increment = statement.getIncrement();
		CStatement init = statement.getInit();
		CStatement guard = statement.getGuard();
		CStatement body = statement.getBody();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		XcfaLocation endLoc = getAnonymousLoc(builder);
		XcfaLocation endInit = getAnonymousLoc(builder);
		XcfaLocation startIncrement = getAnonymousLoc(builder);
		XcfaLocation outerLastTest = getAnonymousLoc(builder);
		builder.addLoc(endLoc);
		propagateMetadata(statement, endLoc);
		builder.addLoc(outerLastTest);
		propagateMetadata(statement, outerLastTest);
		builder.addLoc(endInit);
		propagateMetadata(statement, endInit);
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		builder.addLoc(startIncrement);
		propagateMetadata(statement, startIncrement);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);

		XcfaLocation lastInit = init == null ? initLoc : init.accept(this, new ParamPack(builder, initLoc, null, null, returnLoc));
		XcfaLocation lastTest = guard == null ? lastInit : buildWithoutPostStatement(guard, new ParamPack(builder, lastInit, null, null, returnLoc));
		final AssumeStmt assume = Assume(Neq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
		propagateMetadata(guard, assume);
		xcfaEdge = XcfaEdge.of(lastTest, endInit, guard == null ? List.of() : List.of(Stmt(assume)));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		final AssumeStmt assume1 = Assume(Eq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
		propagateMetadata(guard, assume1);
		xcfaEdge = XcfaEdge.of(lastTest, outerLastTest, guard == null ? List.of() : List.of(Stmt(assume1)));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation innerLastGuard = guard == null ? endInit : buildPostStatement(guard, new ParamPack(builder, endInit, endLoc, startIncrement, returnLoc));
		XcfaLocation lastBody = body == null ? innerLastGuard : body.accept(this, new ParamPack(builder, innerLastGuard, endLoc, startIncrement, returnLoc));
		xcfaEdge = XcfaEdge.of(lastBody, startIncrement, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		if(increment!=null) {
			XcfaLocation lastIncrement = increment.accept(this, new ParamPack(builder, startIncrement, null, null, returnLoc));
			xcfaEdge = XcfaEdge.of(lastIncrement, lastInit, List.of());
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		} else {
			xcfaEdge = XcfaEdge.of(startIncrement, lastInit, List.of());
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		}
		XcfaLocation outerLastGuard = guard == null ? outerLastTest : buildPostStatement(guard, new ParamPack(builder, outerLastTest, endLoc, startIncrement, returnLoc));
		xcfaEdge = XcfaEdge.of(outerLastGuard, endLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		return endLoc;
	}

	@Override
	public XcfaLocation visit(CGoto statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge edge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		edge = XcfaEdge.of(initLoc, getLoc(builder, statement.getLabel()), List.of());
		builder.addLoc(getLoc(builder, statement.getLabel()));
		XcfaLocation unreachableLoc = XcfaLocation.create("Unreachable" + XcfaLocation.uniqeCounter());
		builder.addLoc(unreachableLoc);
		propagateMetadata(statement, unreachableLoc);
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		return unreachableLoc;	}

	@Override
	public XcfaLocation visit(CIf statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		CStatement elseStatement = statement.getElseStatement();
		CStatement body = statement.getBody();
		CStatement guard = statement.getGuard();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		XcfaLocation endLoc = getAnonymousLoc(builder);
		XcfaLocation mainBranch = getAnonymousLoc(builder);
		XcfaLocation elseBranch = getAnonymousLoc(builder);
		builder.addLoc(endLoc);
		propagateMetadata(statement, endLoc);
		builder.addLoc(mainBranch);
		propagateMetadata(statement, mainBranch);
		builder.addLoc(elseBranch);
		propagateMetadata(statement, elseBranch);
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation endGuard = buildWithoutPostStatement(guard, new ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc));
		final AssumeStmt assume = Assume(Neq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
		propagateMetadata(guard, assume);
		xcfaEdge = XcfaEdge.of(endGuard, mainBranch, List.of(Stmt(assume)));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		final AssumeStmt assume1 = Assume(Eq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
		propagateMetadata(guard, assume1);
		xcfaEdge = XcfaEdge.of(endGuard, elseBranch, List.of(Stmt(assume1)));
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);

		XcfaLocation mainAfterGuard = buildPostStatement(guard, new ParamPack(builder, mainBranch, breakLoc, continueLoc, returnLoc));
		XcfaLocation mainEnd = body.accept(this, new ParamPack(builder, mainAfterGuard, breakLoc, continueLoc, returnLoc));
		if(elseStatement != null) {
			XcfaLocation elseAfterGuard = buildPostStatement(guard, new ParamPack(builder, elseBranch, breakLoc, continueLoc, returnLoc));
			XcfaLocation elseEnd = elseStatement.accept(this, new ParamPack(builder, elseAfterGuard, breakLoc, continueLoc, returnLoc));
			xcfaEdge = XcfaEdge.of(elseEnd, endLoc, List.of());
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		} else {
			xcfaEdge = XcfaEdge.of(elseBranch, endLoc, List.of());
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		}

		xcfaEdge = XcfaEdge.of(mainEnd, endLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		return endLoc;	}

	@Override
	public XcfaLocation visit(CInitializerList statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		for (Tuple2<Optional<CStatement>, CStatement> cStatement : statement.getStatements()) {
			lastLoc = cStatement.get2().accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		}
		return lastLoc;
	}

	@Override
	public XcfaLocation visit(CRet statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		CStatement expr = statement.getExpr();

		if(expr == null) return lastLoc;
		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation endExpr = expr.accept(this, new ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc));
		XcfaLocation endLoc = getAnonymousLoc(builder);
		builder.addLoc(endLoc);
		propagateMetadata(statement, endLoc);
		VarDecl<?> key = builder.getParams().entrySet().iterator().next().getKey();
		XcfaEdge edge = XcfaEdge.of(endExpr, returnLoc, List.of(Stmt(Assign(cast(key, key.getType()), cast(CComplexType.getType(key.getRef()).castTo(expr.getExpression()), key.getType())))));
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		return endLoc;	}

	@Override
	public XcfaLocation visit(CSwitch statement, ParamPack param) {
		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		CStatement testValue = statement.getTestValue();
		CStatement body = statement.getBody();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaLocation endLoc = getAnonymousLoc(builder);
		builder.addLoc(endLoc);
		propagateMetadata(statement, endLoc);
		XcfaEdge edge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		XcfaLocation endInit = buildWithoutPostStatement(testValue, new ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc));
		checkState(body instanceof CCompound, "Switch body has to be a CompoundStatement!");
		Expr<BoolType> defaultExpr = True();
		for (CStatement cStatement : ((CCompound) body).getcStatementList()) {
			if(cStatement instanceof CCase) {
				defaultExpr = And(defaultExpr, Neq(testValue.getExpression(), ((CCase) cStatement).getExpr().getExpression()));
			}
		}
		XcfaLocation lastLocation = null;
		for (CStatement cStatement : ((CCompound) body).getcStatementList()) {
			XcfaLocation location = getAnonymousLoc(builder);
			builder.addLoc(location);
			propagateMetadata(statement, location);
			XcfaEdge xcfaEdge;
			if(lastLocation != null) {
				xcfaEdge = XcfaEdge.of(lastLocation, location, List.of());
				builder.addEdge(xcfaEdge);
				propagateMetadata(statement, xcfaEdge);
			}
			if(cStatement instanceof CCase) {
				XcfaLocation afterGuard = buildPostStatement(testValue, new ParamPack(builder, endInit, breakLoc, continueLoc, returnLoc));
				final AssumeStmt assume = Assume(Eq(testValue.getExpression(), ((CCase) cStatement).getExpr().getExpression()));
				propagateMetadata(statement, assume);
				xcfaEdge = XcfaEdge.of(afterGuard, location, List.of(Stmt(assume)));
				builder.addEdge(xcfaEdge);
				propagateMetadata(statement, xcfaEdge);
			} else if(cStatement instanceof CDefault) {
				XcfaLocation afterGuard = buildPostStatement(testValue, new ParamPack(builder, endInit, breakLoc, continueLoc, returnLoc));
				final AssumeStmt assume = Assume(defaultExpr);
				propagateMetadata(statement, assume);
				xcfaEdge = XcfaEdge.of(afterGuard, location, List.of(Stmt(assume)));
				builder.addEdge(xcfaEdge);
				propagateMetadata(statement, xcfaEdge);
			}
			lastLocation = cStatement.accept(this, new ParamPack(builder, location, endLoc, continueLoc, returnLoc));
		}
		if(lastLocation != null) {
			XcfaEdge xcfaEdge = XcfaEdge.of(lastLocation, endLoc, List.of());
			builder.addEdge(xcfaEdge);
			propagateMetadata(statement, xcfaEdge);
		}
		return endLoc;	}

	@Override
	public XcfaLocation visit(CWhile statement, ParamPack param) {
		int UNROLL_COUNT = 0;

		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;

		CStatement guard = statement.getGuard();
		CStatement body = statement.getBody();

		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge xcfaEdge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		XcfaLocation endLoc = getAnonymousLoc(builder);
		builder.addLoc(endLoc);
		propagateMetadata(statement, endLoc);
		XcfaLocation outerBeforeGuard = getAnonymousLoc(builder);
		builder.addLoc(outerBeforeGuard);
		propagateMetadata(statement, outerBeforeGuard);
		for(int i = 0; i < (UNROLL_COUNT == 0 ? 1 : UNROLL_COUNT); ++i) {
			if (((CCompound) body).getcStatementList().size() == 0) {
				final AssumeStmt assume = Assume(Eq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
				propagateMetadata(guard, assume);
				xcfaEdge = XcfaEdge.of(initLoc, endLoc, List.of(Stmt(assume)));
				builder.addEdge(xcfaEdge);
				propagateMetadata(statement, xcfaEdge);
				return endLoc;
			} else {
				XcfaLocation innerLoop = getAnonymousLoc(builder);
				builder.addLoc(innerLoop);
				propagateMetadata(statement, innerLoop);
				XcfaLocation testEndLoc = buildWithoutPostStatement(guard, new ParamPack(builder, initLoc, null, null, returnLoc));
				if(UNROLL_COUNT > 0) {
					initLoc = getAnonymousLoc(builder);
					builder.addLoc(initLoc);
					propagateMetadata(statement, initLoc);
				}
				final AssumeStmt assume = Assume(Neq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
				propagateMetadata(guard, assume);
				xcfaEdge = XcfaEdge.of(testEndLoc, innerLoop, List.of(Stmt(assume)));
				builder.addEdge(xcfaEdge);
				propagateMetadata(statement, xcfaEdge);
				final AssumeStmt assume1 = Assume(Eq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()));
				propagateMetadata(guard, assume1);
				xcfaEdge = XcfaEdge.of(testEndLoc, outerBeforeGuard, List.of(Stmt(assume1)));
				builder.addEdge(xcfaEdge);
				propagateMetadata(statement, xcfaEdge);
				XcfaLocation lastGuard = buildPostStatement(guard, new ParamPack(builder, innerLoop, endLoc, initLoc, returnLoc));
				XcfaLocation lastBody = body.accept(this, new ParamPack(builder, lastGuard, endLoc, initLoc, returnLoc));
				xcfaEdge = XcfaEdge.of(lastBody, initLoc, List.of());
				builder.addEdge(xcfaEdge);
				propagateMetadata(statement, xcfaEdge);
			}
		}
		XcfaLocation outerLastGuard = buildPostStatement(guard, new ParamPack(builder, outerBeforeGuard, null, null, null));
		xcfaEdge = XcfaEdge.of(outerLastGuard, endLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(statement, xcfaEdge);
		return endLoc;
	}

	private XcfaLocation buildWithoutPostStatement(CStatement cStatement, ParamPack param) {
		checkState(cStatement instanceof CCompound, "Currently only CCompounds have pre- and post statements!");
		CCompound statement = (CCompound) cStatement;

		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;
		CStatement preStatements = statement.getPreStatements();
		CStatement postStatements = statement.getPostStatements();
		List<CStatement> cStatementList = statement.getcStatementList();


		XcfaLocation initLoc = getLoc(builder, statement.getId());
		builder.addLoc(initLoc);
		propagateMetadata(statement, initLoc);
		XcfaEdge edge = XcfaEdge.of(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		propagateMetadata(statement, edge);
		lastLoc = initLoc;
		if(preStatements != null) lastLoc = preStatements.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		for (int i = 0; i < cStatementList.size()-1; i++) {
			CStatement stmt = cStatementList.get(i);
			if (stmt != null) lastLoc = stmt.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		}
		if(cStatementList.size() == 0) return lastLoc;
		CStatement lastStatement = cStatementList.get(cStatementList.size() - 1);
		if(postStatements == null) {
			lastLoc = buildWithoutPostStatement(lastStatement, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		} else {
			lastLoc = lastStatement.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		}
		return lastLoc;
	}

	private XcfaLocation buildPostStatement(CStatement cStatement, ParamPack param) {
		checkState(cStatement instanceof CCompound, "Currently only CCompounds have pre- and post statements!");
		CCompound statement = (CCompound) cStatement;

		XcfaProcedure.Builder builder = param.builder;
		XcfaLocation lastLoc = param.lastLoc;
		XcfaLocation breakLoc = param.breakLoc;
		XcfaLocation continueLoc = param.continueLoc;
		XcfaLocation returnLoc = param.returnLoc;
		CStatement preStatements = statement.getPreStatements();
		CStatement postStatements = statement.getPostStatements();
		List<CStatement> cStatementList = statement.getcStatementList();

		if(postStatements != null) lastLoc = postStatements.accept(this, new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		else lastLoc = buildPostStatement(cStatementList.get(cStatementList.size()-1), new ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc));
		return lastLoc;
	}

	public static class ParamPack {
		private final XcfaProcedure.Builder builder;
		private final XcfaLocation lastLoc;
		private final XcfaLocation breakLoc;
		private final XcfaLocation continueLoc;
		private final XcfaLocation returnLoc;

		public ParamPack(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
			this.builder = builder;
			this.lastLoc = lastLoc;
			this.breakLoc = breakLoc;
			this.continueLoc = continueLoc;
			this.returnLoc = returnLoc;
		}

		public XcfaProcedure.Builder getBuilder() {
			return builder;
		}

		public XcfaLocation getLastLoc() {
			return lastLoc;
		}

		public XcfaLocation getBreakLoc() {
			return breakLoc;
		}

		public XcfaLocation getContinueLoc() {
			return continueLoc;
		}

		public XcfaLocation getReturnLoc() {
			return returnLoc;
		}
	}
}
