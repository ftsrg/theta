/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Annotation</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.Annotation#getDeclaration <em>Declaration</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.Annotation#getArguments <em>Arguments</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getAnnotation()
 * @model
 * @generated
 */
public interface Annotation extends EObject
{
	/**
	 * Returns the value of the '<em><b>Declaration</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Declaration</em>' reference.
	 * @see #setDeclaration(AnnotationDeclaration)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAnnotation_Declaration()
	 * @model
	 * @generated
	 */
	AnnotationDeclaration getDeclaration();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.Annotation#getDeclaration <em>Declaration</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Declaration</em>' reference.
	 * @see #getDeclaration()
	 * @generated
	 */
	void setDeclaration(AnnotationDeclaration value);

	/**
	 * Returns the value of the '<em><b>Arguments</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.AnnotationArgument}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Arguments</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAnnotation_Arguments()
	 * @model containment="true"
	 * @generated
	 */
	EList<AnnotationArgument> getArguments();

} // Annotation
