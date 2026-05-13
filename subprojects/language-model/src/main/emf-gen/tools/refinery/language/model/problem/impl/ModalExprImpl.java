/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.language.model.problem.Concreteness;
import tools.refinery.language.model.problem.ModalExpr;
import tools.refinery.language.model.problem.Modality;
import tools.refinery.language.model.problem.ProblemPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Modal Expr</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.ModalExprImpl#getConcreteness <em>Concreteness</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ModalExprImpl#getModality <em>Modality</em>}</li>
 * </ul>
 *
 * @generated
 */
public class ModalExprImpl extends UnaryExprImpl implements ModalExpr
{
	/**
	 * The default value of the '{@link #getConcreteness() <em>Concreteness</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getConcreteness()
	 * @generated
	 * @ordered
	 */
	protected static final Concreteness CONCRETENESS_EDEFAULT = Concreteness.UNSPECIFIED;

	/**
	 * The cached value of the '{@link #getConcreteness() <em>Concreteness</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getConcreteness()
	 * @generated
	 * @ordered
	 */
	protected Concreteness concreteness = CONCRETENESS_EDEFAULT;

	/**
	 * The default value of the '{@link #getModality() <em>Modality</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getModality()
	 * @generated
	 * @ordered
	 */
	protected static final Modality MODALITY_EDEFAULT = Modality.UNSPECIFIED;

	/**
	 * The cached value of the '{@link #getModality() <em>Modality</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getModality()
	 * @generated
	 * @ordered
	 */
	protected Modality modality = MODALITY_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ModalExprImpl()
	{
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass()
	{
		return ProblemPackage.Literals.MODAL_EXPR;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Concreteness getConcreteness()
	{
		return concreteness;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setConcreteness(Concreteness newConcreteness)
	{
		Concreteness oldConcreteness = concreteness;
		concreteness = newConcreteness == null ? CONCRETENESS_EDEFAULT : newConcreteness;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.MODAL_EXPR__CONCRETENESS, oldConcreteness, concreteness));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Modality getModality()
	{
		return modality;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setModality(Modality newModality)
	{
		Modality oldModality = modality;
		modality = newModality == null ? MODALITY_EDEFAULT : newModality;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.MODAL_EXPR__MODALITY, oldModality, modality));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType)
	{
		switch (featureID)
		{
			case ProblemPackage.MODAL_EXPR__CONCRETENESS:
				return getConcreteness();
			case ProblemPackage.MODAL_EXPR__MODALITY:
				return getModality();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eSet(int featureID, Object newValue)
	{
		switch (featureID)
		{
			case ProblemPackage.MODAL_EXPR__CONCRETENESS:
				setConcreteness((Concreteness)newValue);
				return;
			case ProblemPackage.MODAL_EXPR__MODALITY:
				setModality((Modality)newValue);
				return;
		}
		super.eSet(featureID, newValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eUnset(int featureID)
	{
		switch (featureID)
		{
			case ProblemPackage.MODAL_EXPR__CONCRETENESS:
				setConcreteness(CONCRETENESS_EDEFAULT);
				return;
			case ProblemPackage.MODAL_EXPR__MODALITY:
				setModality(MODALITY_EDEFAULT);
				return;
		}
		super.eUnset(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean eIsSet(int featureID)
	{
		switch (featureID)
		{
			case ProblemPackage.MODAL_EXPR__CONCRETENESS:
				return concreteness != CONCRETENESS_EDEFAULT;
			case ProblemPackage.MODAL_EXPR__MODALITY:
				return modality != MODALITY_EDEFAULT;
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString()
	{
		if (eIsProxy()) return super.toString();

		StringBuilder result = new StringBuilder(super.toString());
		result.append(" (concreteness: ");
		result.append(concreteness);
		result.append(", modality: ");
		result.append(modality);
		result.append(')');
		return result.toString();
	}

} //ModalExprImpl
