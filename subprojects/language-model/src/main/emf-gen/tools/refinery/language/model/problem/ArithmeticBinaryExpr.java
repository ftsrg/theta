/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Arithmetic Binary Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ArithmeticBinaryExpr#getOp <em>Op</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getArithmeticBinaryExpr()
 * @model
 * @generated
 */
public interface ArithmeticBinaryExpr extends BinaryExpr
{
	/**
	 * Returns the value of the '<em><b>Op</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.BinaryOp}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.BinaryOp
	 * @see #setOp(BinaryOp)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getArithmeticBinaryExpr_Op()
	 * @model
	 * @generated
	 */
	BinaryOp getOp();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ArithmeticBinaryExpr#getOp <em>Op</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.BinaryOp
	 * @see #getOp()
	 * @generated
	 */
	void setOp(BinaryOp value);

} // ArithmeticBinaryExpr
