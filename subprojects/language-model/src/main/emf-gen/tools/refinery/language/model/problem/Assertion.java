/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Assertion</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.Assertion#isDefault <em>Default</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getAssertion()
 * @model
 * @generated
 */
public interface Assertion extends Statement, AbstractAssertion
{
	/**
	 * Returns the value of the '<em><b>Default</b></em>' attribute.
	 * The default value is <code>"false"</code>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Default</em>' attribute.
	 * @see #setDefault(boolean)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAssertion_Default()
	 * @model default="false"
	 * @generated
	 */
	boolean isDefault();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Assertion#isDefault <em>Default</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Default</em>' attribute.
	 * @see #isDefault()
	 * @generated
	 */
	void setDefault(boolean value);

} // Assertion
