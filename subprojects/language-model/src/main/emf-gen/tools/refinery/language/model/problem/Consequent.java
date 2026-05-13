/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Consequent</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.Consequent#getActions <em>Actions</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getConsequent()
 * @model
 * @generated
 */
public interface Consequent extends EObject
{
	/**
	 * Returns the value of the '<em><b>Actions</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Action}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Actions</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getConsequent_Actions()
	 * @model containment="true"
	 * @generated
	 */
	EList<Action> getActions();

} // Consequent
