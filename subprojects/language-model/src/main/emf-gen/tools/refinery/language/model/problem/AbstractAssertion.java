/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Abstract Assertion</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.AbstractAssertion#getArguments <em>Arguments</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.AbstractAssertion#getRelation <em>Relation</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.AbstractAssertion#getValue <em>Value</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getAbstractAssertion()
 * @model abstract="true"
 * @generated
 */
public interface AbstractAssertion extends ExistentialQuantifier
{
	/**
	 * Returns the value of the '<em><b>Arguments</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.AssertionArgument}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Arguments</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAbstractAssertion_Arguments()
	 * @model containment="true"
	 * @generated
	 */
	EList<AssertionArgument> getArguments();

	/**
	 * Returns the value of the '<em><b>Relation</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Relation</em>' reference.
	 * @see #setRelation(Relation)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAbstractAssertion_Relation()
	 * @model
	 * @generated
	 */
	Relation getRelation();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.AbstractAssertion#getRelation <em>Relation</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Relation</em>' reference.
	 * @see #getRelation()
	 * @generated
	 */
	void setRelation(Relation value);

	/**
	 * Returns the value of the '<em><b>Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Value</em>' containment reference.
	 * @see #setValue(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAbstractAssertion_Value()
	 * @model containment="true"
	 * @generated
	 */
	Expr getValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.AbstractAssertion#getValue <em>Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Value</em>' containment reference.
	 * @see #getValue()
	 * @generated
	 */
	void setValue(Expr value);

} // AbstractAssertion
