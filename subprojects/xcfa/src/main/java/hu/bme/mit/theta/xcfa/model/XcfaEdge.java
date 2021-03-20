package hu.bme.mit.theta.xcfa.model;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;

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

    public static XcfaEdge copyOf(XcfaEdge edge, Map<XcfaLocation, XcfaLocation> locationLut) {
        return new XcfaEdge(locationLut.get(edge.source), locationLut.get(edge.target), edge.stmts);
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
