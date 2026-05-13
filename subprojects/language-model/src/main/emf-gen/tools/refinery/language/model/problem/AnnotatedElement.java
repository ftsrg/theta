/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Annotated Element</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.AnnotatedElement#getAnnotations <em>Annotations</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getAnnotatedElement()
 * @model interface="true" abstract="true"
 * @generated
 */
public interface AnnotatedElement extends EObject
{
	/**
	 * Returns the value of the '<em><b>Annotations</b></em>' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Annotations</em>' containment reference.
	 * @see #setAnnotations(AnnotationContainer)
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAnnotatedElement_Annotations()
	 * @model containment="true"
	 * @generated
	 */
	AnnotationContainer getAnnotations();

	/**
	 * Sets the value of the '{@link tools.refinery.language.model.problem.AnnotatedElement#getAnnotations <em>Annotations</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Annotations</em>' containment reference.
	 * @see #getAnnotations()
	 * @generated
	 */
	void setAnnotations(AnnotationContainer value);

} // AnnotatedElement
