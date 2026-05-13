/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Comparison Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ComparisonExpr#getOp <em>Op</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getComparisonExpr()
 * @model
 * @generated
 */
public interface ComparisonExpr extends BinaryExpr
{
	/**
	 * Returns the value of the '<em><b>Op</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.ComparisonOp}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.ComparisonOp
	 * @see #setOp(ComparisonOp)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getComparisonExpr_Op()
	 * @model
	 * @generated
	 */
	ComparisonOp getOp();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ComparisonExpr#getOp <em>Op</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.ComparisonOp
	 * @see #getOp()
	 * @generated
	 */
	void setOp(ComparisonOp value);

} // ComparisonExpr
