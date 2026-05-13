/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Predicate Definition</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.PredicateDefinition#getBodies <em>Bodies</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.PredicateDefinition#getKind <em>Kind</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.PredicateDefinition#getComputedValue <em>Computed Value</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.PredicateDefinition#getSuperSets <em>Super Sets</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getPredicateDefinition()
 * @model
 * @generated
 */
public interface PredicateDefinition extends ParametricDefinition, Relation
{
	/**
	 * Returns the value of the '<em><b>Bodies</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Conjunction}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Bodies</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getPredicateDefinition_Bodies()
	 * @model containment="true"
	 * @generated
	 */
	EList<Conjunction> getBodies();

	/**
	 * Returns the value of the '<em><b>Kind</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.PredicateKind}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.PredicateKind
	 * @see #setKind(PredicateKind)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getPredicateDefinition_Kind()
	 * @model
	 * @generated
	 */
	PredicateKind getKind();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.PredicateDefinition#getKind <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.PredicateKind
	 * @see #getKind()
	 * @generated
	 */
	void setKind(PredicateKind value);

	/**
	 * Returns the value of the '<em><b>Computed Value</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Computed Value</em>' containment reference.
	 * @see #setComputedValue(PredicateDefinition)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getPredicateDefinition_ComputedValue()
	 * @model containment="true" transient="true"
	 * @generated
	 */
	PredicateDefinition getComputedValue();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.PredicateDefinition#getComputedValue <em>Computed Value</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Computed Value</em>' containment reference.
	 * @see #getComputedValue()
	 * @generated
	 */
	void setComputedValue(PredicateDefinition value);

	/**
	 * Returns the value of the '<em><b>Super Sets</b></em>' reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Relation}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Super Sets</em>' reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getPredicateDefinition_SuperSets()
	 * @model
	 * @generated
	 */
	EList<Relation> getSuperSets();

} // PredicateDefinition
