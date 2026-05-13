/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Existential Quantifier</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ExistentialQuantifier#getImplicitVariables <em>Implicit Variables</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getExistentialQuantifier()
 * @model interface="true" abstract="true"
 * @generated
 */
public interface ExistentialQuantifier extends EObject
{
	/**
	 * Returns the value of the '<em><b>Implicit Variables</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.ImplicitVariable}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Implicit Variables</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getExistentialQuantifier_ImplicitVariables()
	 * @model containment="true" transient="true"
	 * @generated
	 */
	EList<ImplicitVariable> getImplicitVariables();

} // ExistentialQuantifier
