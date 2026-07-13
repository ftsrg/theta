package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import hu.bme.mit.theta.xcfa.model.*;
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager;

import java.util.*;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.*;
import static hu.bme.mit.theta.xcfa.utils.UtilsKt.AssignStmtLabel;


public class SvLibXcfaBuilder extends SvLibBaseVisitor<Void> {

  private final ProcedurePassManager procedurePassManager;

  private final LinkedHashMap<String, VarDecl<?>> declarations = new LinkedHashMap<>();
  private String entryProcedureName;

  private XcfaProcedureBuilder entryProcedure;

  private List<SvLibParser.TermContext> entryArguments = List.of();

  private final List<SvLibParser.RelationalTermContext> postconditions = new ArrayList<>();
  private final Map<String, List<SvLibParser.RelationalTermContext>> checkTrueByTag =
      new LinkedHashMap<>();

  private int procedureCount;

  private int locCounter;

  SvLibXcfaBuilder(ProcedurePassManager procedurePassManager) {
    this.procedurePassManager = procedurePassManager;
  }

  XCFA buildXcfa(SvLibParser.ScriptContext script) {
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
      } else if (command instanceof SvLibParser.SMTLIBv2CommandContext smtlibCommandContext
          && smtlibCommandContext.command()
          instanceof SvLibParser.DeclareConstCommandContext declareConstCommandContext) {
        String name = declareConstCommandContext.cmd_declareConst().symbol().getText();
        VarDecl<?> declaration =
            Var(name, sortOf(declareConstCommandContext.cmd_declareConst().sort()));
        declarations.put(name, declaration);
        SvLibUtils.registerVar(declaration, true);
      } else if (command instanceof SvLibParser.DefineProcContext) {
        procedureCount++;
      } else if (command instanceof SvLibParser.VerifyCallContext verifyCallContext) {
        entryProcedureName = verifyCallContext.symbol().getText();
        entryArguments = List.copyOf(verifyCallContext.term());
      } else if (command instanceof SvLibParser.AnnotateTagContext annotateTagContext) {
        collectAnnotateTagProperties(annotateTagContext.annotateTagCommand());
      }
    }
    if (procedureCount > 1) {
      throw new UnsupportedOperationException(
          "Current SV-LIB prototype supports exactly one procedure");
    }
  }

  private void collectAnnotateTagProperties(SvLibParser.AnnotateTagCommandContext ctx) {
    String tag = ctx.symbol().getText();
    for (SvLibParser.AttributeSvLibContext attribute : ctx.attributeSvLib()) {
      if (attribute instanceof SvLibParser.TagPropertyContext tagPropertyContext
          && tagPropertyContext.property()
          instanceof SvLibParser.EnsuresPropertyContext ensuresPropertyContext) {
        postconditions.add(ensuresPropertyContext.relationalTerm());
      } else if (attribute instanceof SvLibParser.TagPropertyContext tagPropertyContext
          && tagPropertyContext.property()
          instanceof SvLibParser.CheckTruePropertyContext checkTruePropertyContext) {
        checkTrueByTag
            .computeIfAbsent(tag, unused -> new ArrayList<>())
            .add(checkTruePropertyContext.relationalTerm());
      }
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

  private SvLibMetadata metadata(String sourceName) {
    return new SvLibMetadata(sourceName);
  }

  private SvLibMetadata tagMetadata(String tag) {
    return new SvLibMetadata(tag, tag);
  }

  private XcfaLocation nextLoc(String sourceName) {
    return nextLoc(sourceName, false);
  }

  private XcfaLocation nextLoc(String sourceName, boolean tag) {
    return new XcfaLocation("l" + locCounter++, tag ? tagMetadata(sourceName) : metadata(sourceName));
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

    List<XcfaLabel> entryLabels = new ArrayList<>();
    if (Objects.equals(entryProcedureName, name)) {
      List<VarDecl<?>> inputVars = new ArrayList<>();
      for (kotlin.Pair<VarDecl<?>, ParamDirection> param : procedure.getParams()) {
        if (param.getSecond() == ParamDirection.IN) {
          inputVars.add(param.getFirst());
        }
      }
      for (int i = 0; i < Math.min(entryArguments.size(), inputVars.size()); i++) {
        entryLabels.add(
            AssignStmtLabel(
                inputVars.get(i),
                expr(entryArguments.get(i), inputVars.get(i).getType(), procedure, declarations),
                metadata(inputVars.get(i).getName())));
      }
    }

    XcfaLocation start = addLabels(procedure, procedure.getInitLoc(), entryLabels);
    XcfaLocation exit =
        new SvLibStatementVisitor(procedure, declarations, this::nextLoc)
            .visit(
                ctx.statement(), start);

    applyTaggedCheckTrueProperties(procedure);
    checkTrueByTag.clear();

    addExitEdges(procedure, exit);
    this.entryProcedure = procedure;

    return null;
  }

  private void applyTaggedCheckTrueProperties(XcfaProcedureBuilder procedure) {
    if (checkTrueByTag.isEmpty()) {
      return;
    }

    for (XcfaLocation location : new ArrayList<>(procedure.getLocs())) {
      if (!(location.getMetadata() instanceof SvLibMetadata metadata) || !metadata.isTag()) {
        continue;
      }

      List<SvLibParser.RelationalTermContext> checkTrueTerms =
          checkTrueByTag.get(metadata.getTag());
      if (checkTrueTerms == null || checkTrueTerms.isEmpty()) {
        continue;
      }

      insertChecksBeforeOutgoingEdges(procedure, location, checkTrueTerms);
    }
  }

  private void insertChecksBeforeOutgoingEdges(
      XcfaProcedureBuilder procedure,
      XcfaLocation source,
      List<SvLibParser.RelationalTermContext> checkTrueTerms) {
    List<XcfaEdge> originalOutgoingEdges = new ArrayList<>(source.getOutgoingEdges());

    XcfaLocation checkedSource = source;
    for (SvLibParser.RelationalTermContext checkTrueTerm : checkTrueTerms) {
      Expr<BoolType> condition = relationalBoolExpr(checkTrueTerm, procedure, declarations);
      XcfaLocation nextCheckedSource = nextLoc("check-true");

      procedure.addEdge(
          new XcfaEdge(
              checkedSource,
              procedure.getErrorLoc().get(),
              new StmtLabel(AssumeStmt.of(Not(condition))),
              EmptyMetaData.INSTANCE));
      procedure.addEdge(
          new XcfaEdge(
              checkedSource,
              nextCheckedSource,
              new StmtLabel(AssumeStmt.of(condition)),
              EmptyMetaData.INSTANCE));

      checkedSource = nextCheckedSource;
    }

    for (XcfaEdge outgoingEdge : originalOutgoingEdges) {
      procedure.removeEdge(outgoingEdge);
      procedure.addEdge(outgoingEdge.withSource(checkedSource));
    }
  }

  private void addExitEdges(XcfaProcedureBuilder procedure, XcfaLocation exit) {
    XcfaLocation finalSource = exit;

    for (SvLibParser.RelationalTermContext postcondition : postconditions) {
      Expr<BoolType> condition = relationalBoolExpr(postcondition, procedure, declarations);

      procedure.addEdge(
          new XcfaEdge(
              finalSource,
              procedure.getErrorLoc().get(),
              new StmtLabel(AssumeStmt.of(Not(condition))),
              EmptyMetaData.INSTANCE));

      finalSource =
          addLabels(
              procedure,
              finalSource,
              List.of(new StmtLabel(AssumeStmt.of(condition))));
    }

    procedure.addEdge(
        new XcfaEdge(
            finalSource,
            procedure.getFinalLoc().get(),
            NopLabel.INSTANCE,
            EmptyMetaData.INSTANCE));
  }

  @Override
  public Void visitVerifyCall(SvLibParser.VerifyCallContext ctx) {
    entryProcedureName = ctx.symbol().getText();
    entryArguments = List.copyOf(ctx.term());
    return null;
  }



  private XcfaLocation addLabels(
      XcfaProcedureBuilder builder, XcfaLocation from, List<XcfaLabel> labels) {
    if (labels.isEmpty()) {
      return from;
    }
    XcfaLocation to = nextLoc("sequence");
    XcfaLabel label = labels.size() == 1 ? labels.get(0) : new SequenceLabel(labels);
    builder.addEdge(new XcfaEdge(from, to, label, EmptyMetaData.INSTANCE));
    return to;
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
