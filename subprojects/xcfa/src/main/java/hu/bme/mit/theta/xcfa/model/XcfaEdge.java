package hu.bme.mit.theta.xcfa.model;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaEdge {
    private XcfaProcedure parent;
    private final XcfaLocation source;
    private final XcfaLocation target;

    private final List<Stmt> stmts;

    public XcfaEdge(final XcfaLocation source, final XcfaLocation target, final List<Stmt> stmts) {
        this.source = checkNotNull(source);
        this.target = checkNotNull(target);
        this.stmts = ImmutableList.copyOf(stmts);
        source.addOutgoingEdge(this);
        target.addIncomingEdge(this);
    }

    private static final XcfaStmtVarReplacer varReplacer = new XcfaStmtVarReplacer();

    public static XcfaEdge copyOf(XcfaEdge edge, Map<XcfaLocation, XcfaLocation> locationLut, Map<VarDecl<?>, VarDecl<?>> newVarLut, Map<CallStmt, CallStmt> newCallStmts) {
        List<Stmt> newStmts = new ArrayList<>();
        for (Stmt stmt : edge.stmts) {
            Stmt stmt1 = stmt.accept(varReplacer, newVarLut);
            newStmts.add(stmt1);
            if(stmt1 instanceof CallStmt) newCallStmts.put((CallStmt) stmt,(CallStmt) stmt1);
        }
        return new XcfaEdge(locationLut.get(edge.source), locationLut.get(edge.target), newStmts);
    }

    public XcfaLocation getSource() {
        return source;
    }

    public XcfaLocation getTarget() {
        return target;
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder("Edge").add(
                Utils.lispStringBuilder("Source").add(source)
        ).add(
                Utils.lispStringBuilder("Target").add(target)
        ).add(
                Utils.lispStringBuilder("Stmts").addAll(stmts)
        ).toString();
    }

    public XcfaProcedure getParent() {
        return parent;
    }

    void setParent(XcfaProcedure xcfaProcedure) {
        this.parent = xcfaProcedure;
    }
}
