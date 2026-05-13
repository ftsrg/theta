/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Case</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.Case#getCondition <em>Condition</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.Case#getValue <em>Value</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getCase()
 * @model
 * @generated
 */
public interface Case extends EObject
{
	/**
	 * Returns the value of the '<em><b>Condition</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Condition</em>' containment reference.
	 * @see #setCondition(Conjunction)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getCase_Condition()
	 * @model containment="true"
	 * @generated
	 */
	Conjunction getCondition();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Case#getCondition <em>Condition</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Condition</em>' containment reference.
	 * @see #getCondition()
	 * @generated
	 */
	void setCondition(Conjunction value);

	/**
	 * Returns the value of the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Value</em>' containment reference.
	 * @see #setValue(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getCase_Value()
	 * @model containment="true"
	 * @generated
	 */
	Expr getValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Case#getValue <em>Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Value</em>' containment reference.
	 * @see #getValue()
	 * @generated
	 */
	void setValue(Expr value);

} // Case
