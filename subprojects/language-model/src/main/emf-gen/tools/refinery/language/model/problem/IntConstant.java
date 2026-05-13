/**
 */
package tools.refinery.language.model.problem;

import java.math.BigInteger;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Int Constant</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.IntConstant#getIntValue <em>Int Value</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getIntConstant()
 * @model
 * @generated
 */
public interface IntConstant extends Constant
{
	/**
	 * Returns the value of the '<em><b>Int Value</b></em>' attribute.
	 * The default value is <code>"0"</code>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Int Value</em>' attribute.
	 * @see #setIntValue(BigInteger)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getIntConstant_IntValue()
	 * @model default="0"
	 * @generated
	 */
	BigInteger getIntValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.IntConstant#getIntValue <em>Int Value</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Int Value</em>' attribute.
	 * @see #getIntValue()
	 * @generated
	 */
	void setIntValue(BigInteger value);

} // IntConstant
