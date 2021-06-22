package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.transformation.c.FunctionVisitor;

import java.util.Map;

/**
 * Every Program, Function and Statement is a subclass of this base class.
 * Any CStatement might have an id associated with it, in case there was a label in the source code. This also provides
 * an XcfaLocation, which can be used when jumping to this named location via a _goto_ instruction
 */
public abstract class CStatement {
	private String id;
	private XcfaLocation loc;
	protected static int counter = 0;
	protected static int UNROLL_COUNT = 0;

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


	/**
	 * Returns the expression associated with a CStatement, which by default throws an exception, as not all subtypes
	 * will return one. For example, the C language statement `int a = (b = 0, 2)` will create a CCompound statement as
	 * the right-hand side of the assignment, whose associated expression will be 2, but the assignment to b has to come
	 * beforehand.
	 * @return The expression associated with the statement.
	 */
	public Expr<?> getExpression() {
		throw new RuntimeException("Cannot get expression!");
	}

	/**
	 * Builds a custom type of object. This is only used in case of CProgram and CFunction.
	 * @param param Any type of parameter that is used while instantiating the object.
	 * @return The instantiated object (XCFA, XcfaProcedure, etc)
	 */
	public Object build(Object param) {
		throw new RuntimeException("Cannot build CStatement!");
	}

	/**
	 * Instantiates the CStatements _below_ the CFunction hierarchy.
	 * @param builder The procedure builder to create new locations and edges
	 * @param lastLoc The last location to bind the new ones to via edges
	 * @param breakLoc The location to jump to if a break statement is encountered
	 * @param continueLoc The location to jump to if a continue statement is encountered
	 * @param returnLocation The location to jump to if a return statement is encountered
	 * @return New last location to bind the next statement(s) to
	 */
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLocation) {
		throw new RuntimeException("Cannot build CStatement!");
	}

	public XcfaLocation getLoc() {
		return loc;
	}
}
