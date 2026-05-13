/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Unary Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.UnaryExpr#getBody <em>Body</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getUnaryExpr()
 * @model abstract="true"
 * @generated
 */
public interface UnaryExpr extends Expr
{
	/**
	 * Returns the value of the '<em><b>Body</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Body</em>' containment reference.
	 * @see #setBody(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getUnaryExpr_Body()
	 * @model containment="true"
	 * @generated
	 */
	Expr getBody();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.UnaryExpr#getBody <em>Body</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Body</em>' containment reference.
	 * @see #getBody()
	 * @generated
	 */
	void setBody(Expr value);

} // UnaryExpr
