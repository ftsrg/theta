package hu.bme.mit.theta.frontend.svlib;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable.encodeSymbol;
import static hu.bme.mit.theta.xcfa.passes.UtilsKt.changeVars;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTypeTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTypeTransformer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;

import java.util.*;

import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

final class SvLibUtils {

  private static GenericSmtLibSymbolTable initialSymbolTable = new GenericSmtLibSymbolTable();
  private static GenericSmtLibSymbolTable symbolTable;
  private static SmtLibTypeTransformer typeTransformer = new GenericSmtLibTypeTransformer(null);
  private static SmtLibTermTransformer termTransformer =
      new GenericSmtLibTermTransformer(initialSymbolTable);
  private static CharStream charStream;

  private SvLibUtils() {}

  static void init(CharStream cs) {
    initialSymbolTable = new GenericSmtLibSymbolTable();
    typeTransformer = new GenericSmtLibTypeTransformer(null);
    termTransformer = new GenericSmtLibTermTransformer(initialSymbolTable);
    charStream = cs;
  }

  static void resetSymbolTable() {
    symbolTable = new GenericSmtLibSymbolTable(initialSymbolTable);
    termTransformer = new GenericSmtLibTermTransformer(symbolTable);
  }

  static void registerVar(VarDecl<?> var, boolean initial) {
    transformConst(Decls.Const(var.getName(), var.getType()), initial);
  }

  static Expr<BoolType> boolExpr(
      SvLibParser.TermContext term,
      XcfaProcedureBuilder procedure,
      Map<String, VarDecl<?>> declarations) {
    return (Expr<BoolType>) expr(term, Bool(), procedure, declarations);
  }

  static Expr<IntType> intExpr(
      SvLibParser.TermContext term,
      XcfaProcedureBuilder procedure,
      Map<String, VarDecl<?>> declarations) {
    return (Expr<IntType>) expr(term, Int(), procedure, declarations);
  }

  static Expr<BoolType> relationalBoolExpr(
      SvLibParser.RelationalTermContext term,
      XcfaProcedureBuilder procedure,
      Map<String, VarDecl<?>> declarations) {
    return (Expr<BoolType>) relationalExpr(term, Bool(), procedure, declarations);
  }

  static Expr<?> relationalExpr(
      SvLibParser.RelationalTermContext term,
      Type expectedType,
      XcfaProcedureBuilder procedure,
      Map<String, VarDecl<?>> declarations) {
    if (term instanceof SvLibParser.OldRelationalTermContext) {
      return unsupported("relational term 'old'");
    }
    return parseAndReplace(getOriginalText(term), expectedType, procedure, declarations);
  }

  static Expr<?> expr(
      SvLibParser.TermContext term,
      Type expectedType,
      XcfaProcedureBuilder procedure,
      Map<String, VarDecl<?>> declarations) {
    return parseAndReplace(getOriginalText(term), expectedType, procedure, declarations);
  }


  private static Expr<?> parseAndReplace(
      String text,
      Type expectedType,
      XcfaProcedureBuilder procedure,
      Map<String, VarDecl<?>> declarations) {
    Expr<?> expr =
        termTransformer.toExpr(text, expectedType, new SmtLibModel(Collections.emptyMap()));
    var exprVars = new ArrayList<ConstDecl<?>>();
    ExprUtils.collectConstants(expr, exprVars);
    Map<Decl<?>, VarDecl<?>> varsToLocal = new HashMap<>();
    for (Decl<?> var : exprVars) {
      varsToLocal.put(var, resolveVar(var.getName(), procedure, declarations));
    }
    return changeVars(expr, varsToLocal);
  }

  static VarDecl<?> resolveVar(
      String symbol,
      XcfaProcedureBuilder procedure,
      Map<String, VarDecl<?>> declarations) {
    String name = symbol;
    VarDecl<?> variable = null;
    for (VarDecl<?> candidate : procedure.getVars()) {
      if (candidate.getName().equals(name)) {
        variable = candidate;
        break;
      }
    }
    if (variable == null) {
      for (kotlin.Pair<VarDecl<?>, hu.bme.mit.theta.xcfa.model.ParamDirection> param :
          procedure.getParams()) {
        if (param.getFirst().getName().equals(name)) {
          variable = param.getFirst();
          break;
        }
      }
    }
    if (variable == null) {
      variable = declarations.get(name);
    }
    if (variable == null) {
      throw new IllegalStateException("Unknown SV-LIB variable '" + name + "'");
    }
    return variable;
  }


  static String getOriginalText(ParserRuleContext ctx) {
    return charStream.getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
  }

  private static void transformConst(ConstDecl<?> decl, boolean initial) {
    final Type type = decl.getType();

    final Tuple2<List<Type>, Type> extractedTypes = extractTypes(type);
    final List<Type> paramTypes = extractedTypes.get1();
    final Type returnType = extractedTypes.get2();

    final String returnSort = typeTransformer.toSort(returnType);
    final String[] paramSorts =
        paramTypes.stream().map(typeTransformer::toSort).toArray(String[]::new);

    String symbolName = encodeSymbol(decl.getName());
    String symbolDeclaration =
        String.format(
            "(declare-fun %s (%s) %s)",
            symbolName, String.join(" ", paramSorts), returnSort);
    (initial ? initialSymbolTable : symbolTable).put(decl, symbolName, symbolDeclaration);
  }

  private static Tuple2<List<Type>, Type> extractTypes(final Type type) {
    if (type instanceof FuncType<?, ?> funcType) {
      final Type paramType = funcType.getParamType();
      final Type resultType = funcType.getResultType();

      checkArgument(!(paramType instanceof FuncType));

      final Tuple2<List<Type>, Type> subResult = extractTypes(resultType);
      final List<Type> paramTypes = subResult.get1();
      final Type newResultType = subResult.get2();
      final List<Type> newParamTypes =
          ImmutableList.<Type>builder().add(paramType).addAll(paramTypes).build();
      return Tuple2.of(newParamTypes, newResultType);
    } else {
      return Tuple2.of(ImmutableList.of(), type);
    }
  }

  static <T> T unsupported(String what) {
    throw new UnsupportedOperationException("Unsupported SV-LIB " + what);
  }
}

