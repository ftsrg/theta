/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Function Definition</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.FunctionDefinition#getCases <em>Cases</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.FunctionDefinition#getFunctionType <em>Function Type</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.FunctionDefinition#isShadow <em>Shadow</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.FunctionDefinition#getComputedValue <em>Computed Value</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.FunctionDefinition#getDomainPredicate <em>Domain Predicate</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getFunctionDefinition()
 * @model
 * @generated
 */
public interface FunctionDefinition extends ParametricDefinition, Relation
{
	/**
	 * Returns the value of the '<em><b>Cases</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Case}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Cases</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getFunctionDefinition_Cases()
	 * @model containment="true"
	 * @generated
	 */
	EList<Case> getCases();

	/**
	 * Returns the value of the '<em><b>Function Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Function Type</em>' reference.
	 * @see #setFunctionType(Relation)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getFunctionDefinition_FunctionType()
	 * @model
	 * @generated
	 */
	Relation getFunctionType();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.FunctionDefinition#getFunctionType <em>Function Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Function Type</em>' reference.
	 * @see #getFunctionType()
	 * @generated
	 */
	void setFunctionType(Relation value);

	/**
	 * Returns the value of the '<em><b>Shadow</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Shadow</em>' attribute.
	 * @see #setShadow(boolean)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getFunctionDefinition_Shadow()
	 * @model
	 * @generated
	 */
	boolean isShadow();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.FunctionDefinition#isShadow <em>Shadow</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Shadow</em>' attribute.
	 * @see #isShadow()
	 * @generated
	 */
	void setShadow(boolean value);

	/**
	 * Returns the value of the '<em><b>Computed Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Computed Value</em>' containment reference.
	 * @see #setComputedValue(FunctionDefinition)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getFunctionDefinition_ComputedValue()
	 * @model containment="true" transient="true"
	 * @generated
	 */
	FunctionDefinition getComputedValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.FunctionDefinition#getComputedValue <em>Computed Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Computed Value</em>' containment reference.
	 * @see #getComputedValue()
	 * @generated
	 */
	void setComputedValue(FunctionDefinition value);

	/**
	 * Returns the value of the '<em><b>Domain Predicate</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Domain Predicate</em>' containment reference.
	 * @see #setDomainPredicate(PredicateDefinition)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getFunctionDefinition_DomainPredicate()
	 * @model containment="true" transient="true"
	 * @generated
	 */
	PredicateDefinition getDomainPredicate();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.FunctionDefinition#getDomainPredicate <em>Domain Predicate</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Domain Predicate</em>' containment reference.
	 * @see #getDomainPredicate()
	 * @generated
	 */
	void setDomainPredicate(PredicateDefinition value);

} // FunctionDefinition
