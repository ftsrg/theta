/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Logic Constant</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.LogicConstant#getLogicValue <em>Logic Value</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getLogicConstant()
 * @model
 * @generated
 */
public interface LogicConstant extends Constant
{
	/**
	 * Returns the value of the '<em><b>Logic Value</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.LogicValue}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Logic Value</em>' attribute.
	 * @see tools.refinery.language.model.problem.LogicValue
	 * @see #setLogicValue(LogicValue)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getLogicConstant_LogicValue()
	 * @model
	 * @generated
	 */
	LogicValue getLogicValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.LogicConstant#getLogicValue <em>Logic Value</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Logic Value</em>' attribute.
	 * @see tools.refinery.language.model.problem.LogicValue
	 * @see #getLogicValue()
	 * @generated
	 */
	void setLogicValue(LogicValue value);

} // LogicConstant
