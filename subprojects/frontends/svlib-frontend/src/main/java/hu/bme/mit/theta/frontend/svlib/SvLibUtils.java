package hu.bme.mit.theta.frontend.svlib;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable.encodeSymbol;
import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTypeTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTypeTransformer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import java.util.List;
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


  static String getOriginalText(ParserRuleContext ctx) {
    return charStream.getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
  }



  private static Type guessType(SvLibParser.TermContext term) {
    if (term instanceof SvLibParser.SpecConstantTermContext) {
      return Int();
    }
    if (term instanceof SvLibParser.QualIdentifierTermContext identifierTerm) {
      String identifier = identifierTerm.qual_identifer().getText();
      if ("true".equals(identifier) || "false".equals(identifier)) {
        return Bool();
      }
      return Int();
    }
    if (term instanceof SvLibParser.ApplicationTermContext application) {
      String operator = application.qual_identifer().getText();
      return switch (operator) {
        case "=", "distinct", "<", "<=", ">", ">=", "not", "and", "or", "=>" -> Bool();
        default -> Int();
      };
    }
    return Int();
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

