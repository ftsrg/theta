/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Reference Declaration</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.ReferenceDeclaration#getOpposite <em>Opposite</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.ReferenceDeclaration#getMultiplicity <em>Multiplicity</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.ReferenceDeclaration#getKind <em>Kind</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.ReferenceDeclaration#getReferenceType <em>Reference Type</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.ReferenceDeclaration#getInvalidMultiplicity <em>Invalid Multiplicity</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.ReferenceDeclaration#getSuperSets <em>Super Sets</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getReferenceDeclaration()
 * @model
 * @generated
 */
public interface ReferenceDeclaration extends Relation, AnnotatedElement
{
	/**
	 * Returns the value of the '<em><b>Opposite</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Opposite</em>' reference.
	 * @see #setOpposite(ReferenceDeclaration)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getReferenceDeclaration_Opposite()
	 * @model
	 * @generated
	 */
	ReferenceDeclaration getOpposite();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getOpposite <em>Opposite</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Opposite</em>' reference.
	 * @see #getOpposite()
	 * @generated
	 */
	void setOpposite(ReferenceDeclaration value);

	/**
	 * Returns the value of the '<em><b>Multiplicity</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Multiplicity</em>' containment reference.
	 * @see #setMultiplicity(Multiplicity)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getReferenceDeclaration_Multiplicity()
	 * @model containment="true"
	 * @generated
	 */
	Multiplicity getMultiplicity();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getMultiplicity <em>Multiplicity</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Multiplicity</em>' containment reference.
	 * @see #getMultiplicity()
	 * @generated
	 */
	void setMultiplicity(Multiplicity value);

	/**
	 * Returns the value of the '<em><b>Kind</b></em>' attribute.
	 * The literals are from the enumeration {@link tools.refinery.language.model.problem.ReferenceKind}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.ReferenceKind
	 * @see #setKind(ReferenceKind)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getReferenceDeclaration_Kind()
	 * @model
	 * @generated
	 */
	ReferenceKind getKind();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getKind <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Kind</em>' attribute.
	 * @see tools.refinery.language.model.problem.ReferenceKind
	 * @see #getKind()
	 * @generated
	 */
	void setKind(ReferenceKind value);

	/**
	 * Returns the value of the '<em><b>Reference Type</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Reference Type</em>' reference.
	 * @see #setReferenceType(Relation)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getReferenceDeclaration_ReferenceType()
	 * @model
	 * @generated
	 */
	Relation getReferenceType();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getReferenceType <em>Reference Type</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Reference Type</em>' reference.
	 * @see #getReferenceType()
	 * @generated
	 */
	void setReferenceType(Relation value);

	/**
	 * Returns the value of the '<em><b>Invalid Multiplicity</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Invalid Multiplicity</em>' containment reference.
	 * @see #setInvalidMultiplicity(Relation)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getReferenceDeclaration_InvalidMultiplicity()
	 * @model containment="true" transient="true"
	 * @generated
	 */
	Relation getInvalidMultiplicity();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.ReferenceDeclaration#getInvalidMultiplicity <em>Invalid Multiplicity</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Invalid Multiplicity</em>' containment reference.
	 * @see #getInvalidMultiplicity()
	 * @generated
	 */
	void setInvalidMultiplicity(Relation value);

	/**
	 * Returns the value of the '<em><b>Super Sets</b></em>' reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Relation}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Super Sets</em>' reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getReferenceDeclaration_SuperSets()
	 * @model
	 * @generated
	 */
	EList<Relation> getSuperSets();

} // ReferenceDeclaration
