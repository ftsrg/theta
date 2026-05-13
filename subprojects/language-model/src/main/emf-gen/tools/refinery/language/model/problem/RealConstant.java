/**
 */
package tools.refinery.language.model.problem;

import java.math.BigDecimal;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Real Constant</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.RealConstant#getRealValue <em>Real Value</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getRealConstant()
 * @model
 * @generated
 */
public interface RealConstant extends Constant
{
	/**
	 * Returns the value of the '<em><b>Real Value</b></em>' attribute.
	 * The default value is <code>"0.0"</code>.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Real Value</em>' attribute.
	 * @see #setRealValue(BigDecimal)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getRealConstant_RealValue()
	 * @model default="0.0"
	 * @generated
	 */
	BigDecimal getRealValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.RealConstant#getRealValue <em>Real Value</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Real Value</em>' attribute.
	 * @see #getRealValue()
	 * @generated
	 */
	void setRealValue(BigDecimal value);

} // RealConstant
