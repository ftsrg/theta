/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Binary Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.BinaryExpr#getLeft <em>Left</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.BinaryExpr#getRight <em>Right</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getBinaryExpr()
 * @model abstract="true"
 * @generated
 */
public interface BinaryExpr extends Expr
{
	/**
	 * Returns the value of the '<em><b>Left</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Left</em>' containment reference.
	 * @see #setLeft(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getBinaryExpr_Left()
	 * @model containment="true"
	 * @generated
	 */
	Expr getLeft();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.BinaryExpr#getLeft <em>Left</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Left</em>' containment reference.
	 * @see #getLeft()
	 * @generated
	 */
	void setLeft(Expr value);

	/**
	 * Returns the value of the '<em><b>Right</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Right</em>' containment reference.
	 * @see #setRight(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getBinaryExpr_Right()
	 * @model containment="true"
	 * @generated
	 */
	Expr getRight();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.BinaryExpr#getRight <em>Right</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Right</em>' containment reference.
	 * @see #getRight()
	 * @generated
	 */
	void setRight(Expr value);

} // BinaryExpr
