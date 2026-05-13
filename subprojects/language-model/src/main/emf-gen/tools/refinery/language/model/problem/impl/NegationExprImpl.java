/**
 */
package tools.refinery.language.model.problem.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import tools.refinery.language.model.problem.Expr;
import tools.refinery.language.model.problem.ImplicitVariable;
import tools.refinery.language.model.problem.NegationExpr;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.UnaryExpr;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Negation Expr</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.NegationExprImpl#getImplicitVariables <em>Implicit Variables</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.NegationExprImpl#getBody <em>Body</em>}</li>
 * </ul>
 *
 * @generated
 */
public class NegationExprImpl extends ProblemEObjectImpl implements NegationExpr
{
	/**
	 * The cached value of the '{@link #getImplicitVariables() <em>Implicit Variables</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getImplicitVariables()
	 * @generated
	 * @ordered
	 */
	protected EList<ImplicitVariable> implicitVariables;

	/**
	 * The cached value of the '{@link #getBody() <em>Body</em>}' containment reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getBody()
	 * @generated
	 * @ordered
	 */
	protected Expr body;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected NegationExprImpl()
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
		return ProblemPackage.Literals.NEGATION_EXPR;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<ImplicitVariable> getImplicitVariables()
	{
		if (implicitVariables == null)
		{
			implicitVariables = new EObjectContainmentEList<ImplicitVariable>(ImplicitVariable.class, this, ProblemPackage.NEGATION_EXPR__IMPLICIT_VARIABLES);
		}
		return implicitVariables;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public Expr getBody()
	{
		return body;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetBody(Expr newBody, NotificationChain msgs)
	{
		Expr oldBody = body;
		body = newBody;
		if (eNotificationRequired())
		{
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, ProblemPackage.NEGATION_EXPR__BODY, oldBody, newBody);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setBody(Expr newBody)
	{
		if (newBody != body)
		{
			NotificationChain msgs = null;
			if (body != null)
				msgs = ((InternalEObject)body).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.NEGATION_EXPR__BODY, null, msgs);
			if (newBody != null)
				msgs = ((InternalEObject)newBody).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - ProblemPackage.NEGATION_EXPR__BODY, null, msgs);
			msgs = basicSetBody(newBody, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.NEGATION_EXPR__BODY, newBody, newBody));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs)
	{
		switch (featureID)
		{
			case ProblemPackage.NEGATION_EXPR__IMPLICIT_VARIABLES:
				return ((InternalEList<?>)getImplicitVariables()).basicRemove(otherEnd, msgs);
			case ProblemPackage.NEGATION_EXPR__BODY:
				return basicSetBody(null, msgs);
		}
		return super.eInverseRemove(otherEnd, featureID, msgs);
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
			case ProblemPackage.NEGATION_EXPR__IMPLICIT_VARIABLES:
				return getImplicitVariables();
			case ProblemPackage.NEGATION_EXPR__BODY:
				return getBody();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@SuppressWarnings("unchecked")
	@Override
	public void eSet(int featureID, Object newValue)
	{
		switch (featureID)
		{
			case ProblemPackage.NEGATION_EXPR__IMPLICIT_VARIABLES:
				getImplicitVariables().clear();
				getImplicitVariables().addAll((Collection<? extends ImplicitVariable>)newValue);
				return;
			case ProblemPackage.NEGATION_EXPR__BODY:
				setBody((Expr)newValue);
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
			case ProblemPackage.NEGATION_EXPR__IMPLICIT_VARIABLES:
				getImplicitVariables().clear();
				return;
			case ProblemPackage.NEGATION_EXPR__BODY:
				setBody((Expr)null);
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
			case ProblemPackage.NEGATION_EXPR__IMPLICIT_VARIABLES:
				return implicitVariables != null && !implicitVariables.isEmpty();
			case ProblemPackage.NEGATION_EXPR__BODY:
				return body != null;
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int eBaseStructuralFeatureID(int derivedFeatureID, Class<?> baseClass)
	{
		if (baseClass == Expr.class)
		{
			switch (derivedFeatureID)
			{
				default: return -1;
			}
		}
		if (baseClass == UnaryExpr.class)
		{
			switch (derivedFeatureID)
			{
				case ProblemPackage.NEGATION_EXPR__BODY: return ProblemPackage.UNARY_EXPR__BODY;
				default: return -1;
			}
		}
		return super.eBaseStructuralFeatureID(derivedFeatureID, baseClass);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public int eDerivedStructuralFeatureID(int baseFeatureID, Class<?> baseClass)
	{
		if (baseClass == Expr.class)
		{
			switch (baseFeatureID)
			{
				default: return -1;
			}
		}
		if (baseClass == UnaryExpr.class)
		{
			switch (baseFeatureID)
			{
				case ProblemPackage.UNARY_EXPR__BODY: return ProblemPackage.NEGATION_EXPR__BODY;
				default: return -1;
			}
		}
		return super.eDerivedStructuralFeatureID(baseFeatureID, baseClass);
	}

} //NegationExprImpl
