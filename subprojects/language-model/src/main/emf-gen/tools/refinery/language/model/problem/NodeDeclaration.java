/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Node Declaration</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.NodeDeclaration#getNodes <em>Nodes</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.NodeDeclaration#getKind <em>Kind</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getNodeDeclaration()
 * @model
 * @generated
 */
public interface NodeDeclaration extends Statement, AnnotatedElement
{
	/**
	 * Returns the value of the '<em><b>Nodes</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Node}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Nodes</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getNodeDeclaration_Nodes()
	 * @model containment="true"
	 * @generated
	 */
	EList<Node> getNodes();

	/**
	 * Returns the value of the '<em><b>Kind</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.NodeKind}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.NodeKind
	 * @see #setKind(NodeKind)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getNodeDeclaration_Kind()
	 * @model
	 * @generated
	 */
	NodeKind getKind();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.NodeDeclaration#getKind <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.NodeKind
	 * @see #getKind()
	 * @generated
	 */
	void setKind(NodeKind value);

} // NodeDeclaration
