package hu.bme.mit.theta.frontend.svlib;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.unsupported;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import hu.bme.mit.theta.xcfa.model.*;
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;


public class SvLibXcfaBuilder extends SvLibBaseVisitor<Void> {

  private final ProcedurePassManager procedurePassManager;

  private final LinkedHashMap<String, VarDecl<?>> declarations = new LinkedHashMap<>();
  private String entryProcedureName;

  private XcfaProcedureBuilder entryProcedure;

  private List<SvLibParser.TermContext> entryArguments = List.of();

  private int procedureCount;

  private int locCounter;

  SvLibXcfaBuilder(ProcedurePassManager procedurePassManager) {
    this.procedurePassManager = procedurePassManager;
  }

  XCFA buildXcfa(SvLibParser.ScriptContext script){
    collectGlobalsAndEntry(script);
    XcfaBuilder xcfaBuilder = new XcfaBuilder("SvLibXCFA");
    for (VarDecl<?> declaration : declarations.values()) {
      xcfaBuilder.addVar(new XcfaGlobalVar(declaration));
    }
    visit(script);
    if (entryProcedure == null) {
      throw new IllegalStateException("SV-LIB input does not define a procedure");
    }
    xcfaBuilder.addEntryPoint(entryProcedure, Collections.emptyList());
    return xcfaBuilder.build();
  }

  private void collectGlobalsAndEntry(SvLibParser.ScriptContext script) {
    for (SvLibParser.CommandSvLibContext command : script.commandSvLib()) {
      if (command instanceof SvLibParser.DeclareVarContext declareVarContext) {
        String name = declareVarContext.symbol().getText();
        VarDecl<?> declaration = Var(name, sortOf(declareVarContext.sort()));
        declarations.put(name, declaration);
        SvLibUtils.registerVar(declaration, true);
      } else if (command instanceof SvLibParser.DefineProcContext) {
        procedureCount++;
      } else if (command instanceof SvLibParser.VerifyCallContext verifyCallContext) {
        entryProcedureName = verifyCallContext.symbol().getText();
        entryArguments = List.copyOf(verifyCallContext.term());
      }
    }
    if (procedureCount > 1) {
      throw new UnsupportedOperationException(
          "Current SV-LIB prototype supports exactly one procedure");
    }
  }

  //Extract the parameter names and types from the ctx,
  // and then add them to the current procedure as either input or output parameters.
  private void addParams(
      XcfaProcedureBuilder procedure,
      SvLibParser.ProcDeclarationArgumentsContext ctx,
      ParamDirection direction) {
    List<SvLibParser.SymbolContext> symbols = ctx.symbol();
    List<SvLibParser.SortContext> sorts = ctx.sort();
    for (int i = 0; i < symbols.size(); i++) {
      String name = symbols.get(i).getText();
      VarDecl<?> param = Var(name, sortOf(sorts.get(i)));
      procedure.addParam(param, direction);
      SvLibUtils.registerVar(param, false);
    }

  }

  private void addLocals(
      XcfaProcedureBuilder procedure, SvLibParser.ProcDeclarationArgumentsContext ctx) {
    List<SvLibParser.SymbolContext> symbols = ctx.symbol();
    List<SvLibParser.SortContext> sorts = ctx.sort();
    for (int i = 0; i < symbols.size(); i++) {
      String name = symbols.get(i).getText();
      VarDecl<?> local = Var(name, sortOf(sorts.get(i)));
      procedure.addVar(local);
      SvLibUtils.registerVar(local, false);
    }
  }

  private SvLibMetadata metadata() {
    return new SvLibMetadata();
  }
  private XcfaLocation nextLoc() {
    return new XcfaLocation("l" + locCounter++, metadata());
  }

  @Override
  public Void visitDeclareVar(SvLibParser.DeclareVarContext ctx) {
    String name = ctx.symbol().getText();
    declarations.put(name, Var(name, sortOf(ctx.sort())));
    return null;
  }

  @Override
  public Void visitDefineProc(SvLibParser.DefineProcContext ctx) {
    String name = ctx.symbol().getText();
    if (entryProcedureName != null && !entryProcedureName.equals(name)) {
      return null;
    }
    if (entryProcedure != null) {
      return null;
    }
    XcfaProcedureBuilder procedure = new XcfaProcedureBuilder(name, procedurePassManager);
    SvLibUtils.resetSymbolTable();
    addParams(procedure, ctx.procDeclarationArguments(0), ParamDirection.IN);
    addParams(procedure, ctx.procDeclarationArguments(1), ParamDirection.OUT);
    addLocals(procedure, ctx.procDeclarationArguments(2));


    procedure.createInitLoc();
    procedure.createFinalLoc();
    procedure.createErrorLoc();


    //SvLibStatementVisitor statementVisitor =
        //new SvLibStatementVisitor(procedure, name, declarations, this::nextLoc);
    return null;
  }

  @Override
  public Void visitVerifyCall(SvLibParser.VerifyCallContext ctx) {
    entryProcedureName = ctx.symbol().getText();
    entryArguments = List.copyOf(ctx.term());
    return null;
  }

  private static Type sortOf(SvLibParser.SortContext sort) {
    if (sort instanceof SvLibParser.SimpleSortContext simpleSort) {
      return switch (simpleSort.identifier().getText()) {
        case "Int" -> Int();
        case "Bool" -> Bool();
        default -> unsupported("sort '" + sort.getText() + "'");
      };
    }
    return unsupported("sort '" + sort.getText() + "'");
  }



}

