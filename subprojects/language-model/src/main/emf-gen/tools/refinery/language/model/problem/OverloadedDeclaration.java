/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Overloaded Declaration</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.OverloadedDeclaration#isShadow <em>Shadow</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getOverloadedDeclaration()
 * @model
 * @generated
 */
public interface OverloadedDeclaration extends ParametricDefinition, Relation
{
	/**
	 * Returns the value of the '<em><b>Shadow</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Shadow</em>' attribute.
	 * @see #setShadow(boolean)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getOverloadedDeclaration_Shadow()
	 * @model
	 * @generated
	 */
	boolean isShadow();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.OverloadedDeclaration#isShadow <em>Shadow</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Shadow</em>' attribute.
	 * @see #isShadow()
	 * @generated
	 */
	void setShadow(boolean value);

} // OverloadedDeclaration
