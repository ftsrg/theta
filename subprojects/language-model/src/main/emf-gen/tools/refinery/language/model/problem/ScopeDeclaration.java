/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Scope Declaration</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ScopeDeclaration#getTypeScopes <em>Type Scopes</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getScopeDeclaration()
 * @model
 * @generated
 */
public interface ScopeDeclaration extends Statement
{
	/**
	 * Returns the value of the '<em><b>Type Scopes</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.TypeScope}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Type Scopes</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getScopeDeclaration_TypeScopes()
	 * @model containment="true"
	 * @generated
	 */
	EList<TypeScope> getTypeScopes();

} // ScopeDeclaration
