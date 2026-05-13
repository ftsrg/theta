/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Problem</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.Problem#getNodes <em>Nodes</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.Problem#getStatements <em>Statements</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.Problem#getKind <em>Kind</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.Problem#isExplicitKind <em>Explicit Kind</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getProblem()
 * @model
 * @generated
 */
public interface Problem extends NamedElement
{
	/**
	 * Returns the value of the '<em><b>Nodes</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Node}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Nodes</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getProblem_Nodes()
	 * @model containment="true" transient="true"
	 * @generated
	 */
	EList<Node> getNodes();

	/**
	 * Returns the value of the '<em><b>Statements</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Statement}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Statements</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getProblem_Statements()
	 * @model containment="true"
	 * @generated
	 */
	EList<Statement> getStatements();

	/**
	 * Returns the value of the '<em><b>Kind</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.ModuleKind}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.ModuleKind
	 * @see #setKind(ModuleKind)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getProblem_Kind()
	 * @model
	 * @generated
	 */
	ModuleKind getKind();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Problem#getKind <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.ModuleKind
	 * @see #getKind()
	 * @generated
	 */
	void setKind(ModuleKind value);

	/**
	 * Returns the value of the '<em><b>Explicit Kind</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Explicit Kind</em>' attribute.
	 * @see #setExplicitKind(boolean)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getProblem_ExplicitKind()
	 * @model transient="true"
	 * @generated
	 */
	boolean isExplicitKind();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Problem#isExplicitKind <em>Explicit Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Explicit Kind</em>' attribute.
	 * @see #isExplicitKind()
	 * @generated
	 */
	void setExplicitKind(boolean value);

} // Problem
