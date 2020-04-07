package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;

public class XSTSVisitor extends XstsDslBaseVisitor<Expr> {

    XSTS xsts;
    HashMap<String,Integer> literalToIntMap=new HashMap<String,Integer>();

    public HashMap<String, Integer> getLiteralToIntMap() {
        return literalToIntMap;
    }

    HashMap<String,VarDecl> nameToDeclMap=new HashMap<String, VarDecl>();

    public XSTS getXsts(){
        return xsts;
    }

    private HashSet<TypeDecl> types=new HashSet<TypeDecl>();

    @Override
    public Expr visitXsts(XstsDslParser.XstsContext ctx) {

        for(XstsDslParser.TypeDeclarationContext typeDecl: ctx.typeDeclarations){
            visitTypeDeclaration(typeDecl);
        }
        for(TypeDecl decl:types){
            for(int i=0;i<decl.getLiterals().size();i++) if(!literalToIntMap.containsKey(decl.getLiterals().get(i)))literalToIntMap.put(decl.getLiterals().get(i),i);
        }
        for(XstsDslParser.VariableDeclarationContext varDecl: ctx.variableDeclarations){
            visitVariableDeclaration(varDecl);
        }
        xsts=new XSTS(types, processNonDetAction(ctx.transitions), processNonDetAction(ctx.initAction), processSequentialAction(ctx.envAction));
        System.out.println(xsts.getVars());
        for(TypeDecl typeDecl:xsts.getTypes()){
            System.out.println(typeDecl);
            for(String literal:typeDecl.getLiterals()){
                System.out.println(literal+" "+literalToIntMap.get(literal));
            }
        }
        for(Stmt stmt: xsts.getTransitions().getStmts()){
            System.out.println(stmt);
        }
        return null;
    }

    @Override
    public Expr visitTypeDeclaration(XstsDslParser.TypeDeclarationContext ctx) {
        List<String> literals=new ArrayList<String>();
        for(XstsDslParser.TypeLiteralContext literal:ctx.literals){
            literals.add(literal.name.getText());
        }
        TypeDecl decl=new TypeDecl(ctx.name.getText(),literals);
        types.add(decl);
        return null;
    }

    @Override
    public Expr visitVariableDeclaration(XstsDslParser.VariableDeclarationContext ctx) {
        Type type;
        if(ctx.type.BOOL()!=null) type= BoolType.getInstance();
        else if(ctx.type.INT()!=null) type= IntType.getInstance();
        else type=IntType.getInstance();
        VarDecl decl=Decls.Var(ctx.name.getText(),type);
        if(nameToDeclMap.containsKey(ctx.name.getText())){
            System.out.println("Variable ["+ctx.name.getText()+"] already exists.");
        }else {
            xsts.getVars().add(decl);
            nameToDeclMap.put(decl.getName(), decl);
        }
        return null;
    }

    @Override
    public Expr visitImplyExpression(XstsDslParser.ImplyExpressionContext ctx) {
        if(ctx.ops.size()>1){
            return Imply(visitOrExpr(ctx.ops.get(0)),visitOrExpr(ctx.ops.get(1)));
        }else return visitOrExpr(ctx.ops.get(0));
    }

    @Override
    public Expr visitOrExpr(XstsDslParser.OrExprContext ctx) {
        if(ctx.ops.size()==1) return visitAndExpr(ctx.ops.get(0));
        List<Expr<BoolType>> ops=new ArrayList<Expr<BoolType>>();
        for(XstsDslParser.AndExprContext child: ctx.ops){
            ops.add(visitAndExpr(child));
        }
        return Or(ops);
    }

    @Override
    public Expr<BoolType> visitAndExpr(XstsDslParser.AndExprContext ctx) {
        if(ctx.ops.size()==1) return visitNotExpr(ctx.ops.get(0));
        List<Expr<BoolType>> ops=new ArrayList<Expr<BoolType>>();
        for(XstsDslParser.NotExprContext child: ctx.ops){
            ops.add(visitNotExpr(child));
        }
        return And(ops);
    }

    @Override
    public Expr<BoolType> visitNotExpr(XstsDslParser.NotExprContext ctx) {
        if(ctx.ops.size()>0) return Not(visitNotExpr(ctx.ops.get(0)));
        else return visitEqExpr(ctx.eqExpr());
    }

    @Override
    public Expr visitEqExpr(XstsDslParser.EqExprContext ctx) {
        if(ctx.ops.size()>1){
            if(ctx.oper.EQ()!=null) return Eq(visitRelationExpr(ctx.ops.get(0)),visitRelationExpr(ctx.ops.get(1)));
            else return Neq(visitRelationExpr(ctx.ops.get(0)),visitRelationExpr(ctx.ops.get(1)));
        }else return visitRelationExpr(ctx.ops.get(0));
    }

    @Override
    public Expr visitEqOperator(XstsDslParser.EqOperatorContext ctx) {
        return super.visitEqOperator(ctx);
    }

    @Override
    public Expr visitRelationExpr(XstsDslParser.RelationExprContext ctx) {
        if(ctx.ops.size()>1){
            if(ctx.oper.LEQ()!=null){
                return Leq(visitAdditiveExpr(ctx.ops.get(0)),visitAdditiveExpr(ctx.ops.get(1)));
            }else if(ctx.oper.GEQ()!=null){
                return Geq(visitAdditiveExpr(ctx.ops.get(0)),visitAdditiveExpr(ctx.ops.get(1)));
            }else if(ctx.oper.LT()!=null){
                return Lt(visitAdditiveExpr(ctx.ops.get(0)),visitAdditiveExpr(ctx.ops.get(1)));
            }else return Gt(visitAdditiveExpr(ctx.ops.get(0)),visitAdditiveExpr(ctx.ops.get(1)));
        }else return visitAdditiveExpr(ctx.ops.get(0));
    }

    @Override
    public Expr visitRelationOperator(XstsDslParser.RelationOperatorContext ctx) {
        return super.visitRelationOperator(ctx);
    }

    @Override
    public Expr visitAdditiveExpr(XstsDslParser.AdditiveExprContext ctx) {
        Expr res=visitMultiplicativeExpr(ctx.ops.get(0));
        for(int i=1;i<ctx.ops.size();i++){
            if(ctx.opers.get(i-1).PLUS()!=null){
                res=Add(res,visitMultiplicativeExpr(ctx.ops.get(i)));
            }else{
                res=Sub(res,visitMultiplicativeExpr(ctx.ops.get(i)));
            }
        }
        return res;

    }

    @Override
    public Expr visitAdditiveOperator(XstsDslParser.AdditiveOperatorContext ctx) {
        return super.visitAdditiveOperator(ctx);
    }

    @Override
    public Expr visitMultiplicativeExpr(XstsDslParser.MultiplicativeExprContext ctx) {
        Expr res=visitNegExpr(ctx.ops.get(0));
        for(int i=1;i<ctx.ops.size();i++){
            if(ctx.opers.get(i-1).DIV()!=null){
                res=Div(res,visitNegExpr(ctx.ops.get(i)));
            }else if(ctx.opers.get(i-1).MOD()!=null){
                res=Mod(res,visitNegExpr(ctx.ops.get(i)));
            }else{
                res=Mul(res,visitNegExpr(ctx.ops.get(i)));
            }
        }
        return res;
    }

    @Override
    public Expr visitMultiplicativeOperator(XstsDslParser.MultiplicativeOperatorContext ctx) {
        return super.visitMultiplicativeOperator(ctx);
    }

    @Override
    public Expr visitNegExpr(XstsDslParser.NegExprContext ctx) {
        if(ctx.ops.size()>0){
            return Neg(visitNegExpr(ctx.ops.get(0)));
        }else return visitPrimaryExpr(ctx.primaryExpr());
    }

    @Override
    public Expr visitPrimaryExpr(XstsDslParser.PrimaryExprContext ctx) {
        if(ctx.value()!=null) return visitValue(ctx.value());
        else return visitParenExpr(ctx.parenExpr());
    }

    @Override
    public Expr visitParenExpr(XstsDslParser.ParenExprContext ctx) {
        if(ctx.prime()!=null) return visitPrime(ctx.prime());
        else return visitImplyExpression(ctx.ops.get(0));
    }

    @Override
    public Expr visitValue(XstsDslParser.ValueContext ctx) {
        if(ctx.literal()!=null) return visitLiteral(ctx.literal());
        else return visitReference(ctx.reference());
    }

    @Override
    public Expr visitLiteral(XstsDslParser.LiteralContext ctx) {
        if(ctx.BOOLLIT()!=null){
            if(ctx.BOOLLIT().getText().equals("true")) return True(); else return False();
        }else{
            return Int(Integer.parseInt(ctx.INTLIT().getText()));
        }
    }

    @Override
    public Expr visitReference(XstsDslParser.ReferenceContext ctx) {
        if(literalToIntMap.containsKey(ctx.name.getText())) return Int(literalToIntMap.get(ctx.name.getText()));
        else return nameToDeclMap.get(ctx.name.getText()).getRef();
    }

    @Override
    public Expr visitPrime(XstsDslParser.PrimeContext ctx) {
        if(ctx.reference()!=null) return visitReference(ctx.reference());
        else return Prime(visitPrime(ctx.prime()));
    }

    public Stmt processAction(XstsDslParser.ActionContext ctx) {
        if(ctx.assignAction()!=null) return processAssignAction(ctx.assignAction());
        else if(ctx.assumeAction()!=null) return processAssumeAction(ctx.assumeAction());
        else if(ctx.havocAction()!=null) return processHavocAction(ctx.havocAction());
        else return processNonDetAction(ctx.nonDetAction());
    }

    public NonDetStmt processNonDetAction(XstsDslParser.NonDetActionContext ctx) {
        List<Stmt> choices=new ArrayList<Stmt>();
        for(XstsDslParser.SequentialActionContext seq:ctx.choices){
            choices.add(processSequentialAction(seq));
        }
        return NonDetStmt.of(choices);
    }

    public SequenceStmt processSequentialAction(XstsDslParser.SequentialActionContext ctx) {
        List<Stmt> stmts=new ArrayList<Stmt>();
        for(XstsDslParser.ActionContext action:ctx.actions){
            stmts.add(processAction(action));
        }
        return SequenceStmt.of(stmts);
    }

    public AssumeStmt processAssumeAction(XstsDslParser.AssumeActionContext ctx) {
        return Stmts.Assume(visitImplyExpression(ctx.cond));
    }

    public AssignStmt processAssignAction(XstsDslParser.AssignActionContext ctx) {
        return Stmts.Assign(processAssignLHS(ctx.lhs),visitImplyExpression(ctx.rhs));
    }

    public HavocStmt processHavocAction(XstsDslParser.HavocActionContext ctx){
        return Stmts.Havoc(nameToDeclMap.get(ctx.name.getText()));
    }

    public VarDecl processAssignLHS(XstsDslParser.PrimeContext ctx){
        XstsDslParser.PrimeContext running=ctx;
        while(running.inner!=null) running=running.inner;
        return nameToDeclMap.get(running.ref.name.getText());
    }
}
