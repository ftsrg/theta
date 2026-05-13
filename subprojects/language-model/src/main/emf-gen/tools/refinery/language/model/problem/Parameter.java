/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Parameter</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.Parameter#getParameterType <em>Parameter Type</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.Parameter#getKind <em>Kind</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getParameter()
 * @model
 * @generated
 */
public interface Parameter extends Variable, AnnotatedElement
{
	/**
	 * Returns the value of the '<em><b>Parameter Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Parameter Type</em>' reference.
	 * @see #setParameterType(Relation)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getParameter_ParameterType()
	 * @model
	 * @generated
	 */
	Relation getParameterType();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Parameter#getParameterType <em>Parameter Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Parameter Type</em>' reference.
	 * @see #getParameterType()
	 * @generated
	 */
	void setParameterType(Relation value);

	/**
	 * Returns the value of the '<em><b>Kind</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.ParameterKind}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.ParameterKind
	 * @see #setKind(ParameterKind)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getParameter_Kind()
	 * @model
	 * @generated
	 */
	ParameterKind getKind();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Parameter#getKind <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.ParameterKind
	 * @see #getKind()
	 * @generated
	 */
	void setKind(ParameterKind value);

} // Parameter
