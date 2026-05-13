/**
 */
package tools.refinery.language.model.problem;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Annotation Container</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.AnnotationContainer#getAnnotations <em>Annotations</em>}</li>
 * </ul>
 *
 * @see tools.refinery.language.model.problem.ProblemPackage#getAnnotationContainer()
 * @model
 * @generated
 */
public interface AnnotationContainer extends Statement
{
	/**
	 * Returns the value of the '<em><b>Annotations</b></em>' containment reference list.
	 * The list contents are of type {@link tools.refinery.language.model.problem.Annotation}.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Annotations</em>' containment reference list.
	 * @see tools.refinery.language.model.problem.ProblemPackage#getAnnotationContainer_Annotations()
	 * @model containment="true"
	 * @generated
	 */
	EList<Annotation> getAnnotations();

} // AnnotationContainer
