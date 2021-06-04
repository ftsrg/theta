package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.transformation.c.FunctionVisitor;

import java.util.Map;

public abstract class CStatement {
	private String id;
	private XcfaLocation loc;
	protected static int counter = 0;

	public String getId() {
		return id;
	}

	public void setId(String id) {
		this.loc = new XcfaLocation(id, Map.of());
		this.id = id;
		FunctionVisitor.locLUT.put(id, loc);
	}

	protected <T> void propagateMetadata(T newOwner) {
		XcfaMetadata.create(newOwner, "sourceStatement", this);
	}


	public Expr<?> getExpression() {
		throw new RuntimeException("Cannot get expression!");
	}

	public Object build(Object param) {
		throw new RuntimeException("Cannot build CStatement!");
	}

	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLocation) {
		throw new RuntimeException("Cannot build CStatement!");
	}

	public XcfaLocation getLoc() {
		return loc;
	}
}
