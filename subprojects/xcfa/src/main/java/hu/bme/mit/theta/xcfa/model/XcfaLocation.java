package hu.bme.mit.theta.xcfa.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaLocation {
    private XcfaProcedure parent;

    private final String name;
    private boolean isErrorLoc = false;
    private boolean isEndLoc = false;
    private final Map<String, String> dictionary;
    private final List<XcfaEdge> incomingEdges;
    private final List<XcfaEdge> outgoingEdges;

    public XcfaLocation(final String name, final Map<String, String> dictionary) {
        this.name = checkNotNull(name);
        this.dictionary = dictionary;
        outgoingEdges = new ArrayList<>();
        incomingEdges = new ArrayList<>();
    }

    public static XcfaLocation copyOf(final XcfaLocation from) {
        return new XcfaLocation(from.getName(), Map.copyOf(from.dictionary));
    }

    public String getName() {
        return name;
    }

    public Map<String, String> getDictionary() {
        return dictionary;
    }

    public List<XcfaEdge> getIncomingEdges() {
        return Collections.unmodifiableList(incomingEdges);
    }

    void addIncomingEdge(XcfaEdge edge) {
        incomingEdges.add(edge);
    }

    public List<XcfaEdge> getOutgoingEdges() {
        return Collections.unmodifiableList(outgoingEdges);
    }

    void addOutgoingEdge(XcfaEdge edge) {
        outgoingEdges.add(edge);
    }

    @Override
    public String toString() {
        return name;
    }

    public boolean isErrorLoc() {
        return isErrorLoc;
    }

    public void setErrorLoc(boolean errorLoc) {
        isErrorLoc = errorLoc;
    }

    public boolean isEndLoc() {
        return isEndLoc;
    }

    public void setEndLoc(boolean endLoc) {
        isEndLoc = endLoc;
    }

    public XcfaProcedure getParent() {
        return parent;
    }

    void setParent(XcfaProcedure xcfaProcedure) {
        this.parent = xcfaProcedure;
    }
}
