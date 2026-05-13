/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Type Scope</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.TypeScope#isIncrement <em>Increment</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.TypeScope#getMultiplicity <em>Multiplicity</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.TypeScope#getTargetType <em>Target Type</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getTypeScope()
 * @model
 * @generated
 */
public interface TypeScope extends EObject
{
	/**
	 * Returns the value of the '<em><b>Increment</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Increment</em>' attribute.
	 * @see #setIncrement(boolean)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getTypeScope_Increment()
	 * @model
	 * @generated
	 */
	boolean isIncrement();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.TypeScope#isIncrement <em>Increment</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Increment</em>' attribute.
	 * @see #isIncrement()
	 * @generated
	 */
	void setIncrement(boolean value);

	/**
	 * Returns the value of the '<em><b>Multiplicity</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Multiplicity</em>' containment reference.
	 * @see #setMultiplicity(Multiplicity)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getTypeScope_Multiplicity()
	 * @model containment="true"
	 * @generated
	 */
	Multiplicity getMultiplicity();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.TypeScope#getMultiplicity <em>Multiplicity</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Multiplicity</em>' containment reference.
	 * @see #getMultiplicity()
	 * @generated
	 */
	void setMultiplicity(Multiplicity value);

	/**
	 * Returns the value of the '<em><b>Target Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Target Type</em>' reference.
	 * @see #setTargetType(Relation)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getTypeScope_TargetType()
	 * @model
	 * @generated
	 */
	Relation getTargetType();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.TypeScope#getTargetType <em>Target Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Target Type</em>' reference.
	 * @see #getTargetType()
	 * @generated
	 */
	void setTargetType(Relation value);

} // TypeScope
