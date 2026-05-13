/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Node Assertion Argument</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.NodeAssertionArgument#getNode <em>Node</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getNodeAssertionArgument()
 * @model
 * @generated
 */
public interface NodeAssertionArgument extends AssertionArgument
{
	/**
	 * Returns the value of the '<em><b>Node</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Node</em>' reference.
	 * @see #setNode(VariableOrNode)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getNodeAssertionArgument_Node()
	 * @model
	 * @generated
	 */
	VariableOrNode getNode();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.NodeAssertionArgument#getNode <em>Node</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Node</em>' reference.
	 * @see #getNode()
	 * @generated
	 */
	void setNode(VariableOrNode value);

} // NodeAssertionArgument
