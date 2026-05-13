/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Rule Definition</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.RuleDefinition#getConsequents <em>Consequents</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.RuleDefinition#getPreconditions <em>Preconditions</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.RuleDefinition#getKind <em>Kind</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getRuleDefinition()
 * @model
 * @generated
 */
public interface RuleDefinition extends ParametricDefinition, NamedElement
{
	/**
	 * Returns the value of the '<em><b>Consequents</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Consequent}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Consequents</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getRuleDefinition_Consequents()
	 * @model containment="true"
	 * @generated
	 */
	EList<Consequent> getConsequents();

	/**
	 * Returns the value of the '<em><b>Preconditions</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Conjunction}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Preconditions</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getRuleDefinition_Preconditions()
	 * @model containment="true"
	 * @generated
	 */
	EList<Conjunction> getPreconditions();

	/**
	 * Returns the value of the '<em><b>Kind</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.RuleKind}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.RuleKind
	 * @see #setKind(RuleKind)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getRuleDefinition_Kind()
	 * @model
	 * @generated
	 */
	RuleKind getKind();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.RuleDefinition#getKind <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.RuleKind
	 * @see #getKind()
	 * @generated
	 */
	void setKind(RuleKind value);

} // RuleDefinition
