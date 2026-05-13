/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Lattice Binary Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.LatticeBinaryExpr#getOp <em>Op</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getLatticeBinaryExpr()
 * @model
 * @generated
 */
public interface LatticeBinaryExpr extends BinaryExpr
{
	/**
	 * Returns the value of the '<em><b>Op</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.LatticeBinaryOp}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.LatticeBinaryOp
	 * @see #setOp(LatticeBinaryOp)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getLatticeBinaryExpr_Op()
	 * @model
	 * @generated
	 */
	LatticeBinaryOp getOp();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.LatticeBinaryExpr#getOp <em>Op</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Op</em>' attribute.
	 * @see tools.refinery.language.model.problem.LatticeBinaryOp
	 * @see #getOp()
	 * @generated
	 */
	void setOp(LatticeBinaryOp value);

} // LatticeBinaryExpr
