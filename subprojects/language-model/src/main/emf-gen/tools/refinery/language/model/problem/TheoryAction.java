/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Theory Action</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.TheoryAction#getTerm <em>Term</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getTheoryAction()
 * @model
 * @generated
 */
public interface TheoryAction extends Action, ExistentialQuantifier
{
	/**
	 * Returns the value of the '<em><b>Term</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Term</em>' containment reference.
	 * @see #setTerm(Expr)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getTheoryAction_Term()
	 * @model containment="true"
	 * @generated
	 */
	Expr getTerm();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.TheoryAction#getTerm <em>Term</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Term</em>' containment reference.
	 * @see #getTerm()
	 * @generated
	 */
	void setTerm(Expr value);

} // TheoryAction
