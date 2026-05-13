/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Arithmetic Unary Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ArithmeticUnaryExpr#getOp <em>Op</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getArithmeticUnaryExpr()
 * @model
 * @generated
 */
public interface ArithmeticUnaryExpr extends UnaryExpr
{
	/**
	 * Returns the value of the '<em><b>Op</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.UnaryOp}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.UnaryOp
	 * @see #setOp(UnaryOp)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getArithmeticUnaryExpr_Op()
	 * @model
	 * @generated
	 */
	UnaryOp getOp();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ArithmeticUnaryExpr#getOp <em>Op</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.UnaryOp
	 * @see #getOp()
	 * @generated
	 */
	void setOp(UnaryOp value);

} // ArithmeticUnaryExpr
