/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Exact Multiplicity</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ExactMultiplicity#getExactValue <em>Exact Value</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getExactMultiplicity()
 * @model
 * @generated
 */
public interface ExactMultiplicity extends Multiplicity
{
	/**
	 * Returns the value of the '<em><b>Exact Value</b></em>' attribute.
	 * The default value is <code>"1"</code>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Exact Value</em>' attribute.
	 * @see #setExactValue(int)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getExactMultiplicity_ExactValue()
	 * @model default="1"
	 * @generated
	 */
	int getExactValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ExactMultiplicity#getExactValue <em>Exact Value</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Exact Value</em>' attribute.
	 * @see #getExactValue()
	 * @generated
	 */
	void setExactValue(int value);

} // ExactMultiplicity
