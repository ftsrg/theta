/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Modal Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ModalExpr#getConcreteness <em>Concreteness</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.ModalExpr#getModality <em>Modality</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getModalExpr()
 * @model
 * @generated
 */
public interface ModalExpr extends UnaryExpr
{
	/**
	 * Returns the value of the '<em><b>Concreteness</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.Concreteness}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Concreteness</em>' attribute.
	 * @see tools.refinery.language.model.problem.Concreteness
	 * @see #setConcreteness(Concreteness)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getModalExpr_Concreteness()
	 * @model
	 * @generated
	 */
	Concreteness getConcreteness();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ModalExpr#getConcreteness <em>Concreteness</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Concreteness</em>' attribute.
	 * @see tools.refinery.language.model.problem.Concreteness
	 * @see #getConcreteness()
	 * @generated
	 */
	void setConcreteness(Concreteness value);

	/**
	 * Returns the value of the '<em><b>Modality</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.Modality}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Modality</em>' attribute.
	 * @see tools.refinery.language.model.problem.Modality
	 * @see #setModality(Modality)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getModalExpr_Modality()
	 * @model
	 * @generated
	 */
	Modality getModality();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ModalExpr#getModality <em>Modality</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Modality</em>' attribute.
	 * @see tools.refinery.language.model.problem.Modality
	 * @see #getModality()
	 * @generated
	 */
	void setModality(Modality value);

} // ModalExpr
