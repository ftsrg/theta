/**
 */
package tools.refinery.language.model.problem;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Variable Or Node Expr</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getVariableOrNode <em>Variable Or Node</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getSingletonVariable <em>Singleton Variable</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getRelation <em>Relation</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getElement <em>Element</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getVariableOrNodeExpr()
 * @model
 * @generated
 */
public interface VariableOrNodeExpr extends Expr
{
	/**
	 * Returns the value of the '<em><b>Variable Or Node</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Variable Or Node</em>' reference.
	 * @see #setVariableOrNode(VariableOrNode)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getVariableOrNodeExpr_VariableOrNode()
	 * @model transient="true" volatile="true" derived="true"
	 *        annotation="https://refinery.tools/emf/2024/ProblemDelegate"
	 * @generated
	 */
	VariableOrNode getVariableOrNode();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getVariableOrNode <em>Variable Or Node</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Variable Or Node</em>' reference.
	 * @see #getVariableOrNode()
	 * @generated
	 */
	void setVariableOrNode(VariableOrNode value);

	/**
	 * Returns the value of the '<em><b>Singleton Variable</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Singleton Variable</em>' containment reference.
	 * @see #setSingletonVariable(ImplicitVariable)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getVariableOrNodeExpr_SingletonVariable()
	 * @model containment="true"
	 * @generated
	 */
	ImplicitVariable getSingletonVariable();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getSingletonVariable <em>Singleton Variable</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Singleton Variable</em>' containment reference.
	 * @see #getSingletonVariable()
	 * @generated
	 */
	void setSingletonVariable(ImplicitVariable value);

	/**
	 * Returns the value of the '<em><b>Relation</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Relation</em>' reference.
	 * @see #setRelation(Relation)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getVariableOrNodeExpr_Relation()
	 * @model transient="true" volatile="true" derived="true"
	 *        annotation="https://refinery.tools/emf/2024/ProblemDelegate"
	 * @generated
	 */
	Relation getRelation();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getRelation <em>Relation</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Relation</em>' reference.
	 * @see #getRelation()
	 * @generated
	 */
	void setRelation(Relation value);

	/**
	 * Returns the value of the '<em><b>Element</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Element</em>' reference.
	 * @see #setElement(NamedElement)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getVariableOrNodeExpr_Element()
	 * @model
	 * @generated
	 */
	NamedElement getElement();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.VariableOrNodeExpr#getElement <em>Element</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Element</em>' reference.
	 * @see #getElement()
	 * @generated
	 */
	void setElement(NamedElement value);

} // VariableOrNodeExpr
