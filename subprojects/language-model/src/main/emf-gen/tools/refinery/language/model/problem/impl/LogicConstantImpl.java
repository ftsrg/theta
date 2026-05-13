/**
 */
package tools.refinery.language.model.problem.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import tools.refinery.language.model.problem.LogicConstant;
import tools.refinery.language.model.problem.LogicValue;
import tools.refinery.language.model.problem.ProblemPackage;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Logic Constant</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.LogicConstantImpl#getLogicValue <em>Logic Value</em>}</li>
 * </ul>
 *
 * @generated
 */
public class LogicConstantImpl extends ConstantImpl implements LogicConstant
{
	/**
	 * The default value of the '{@link #getLogicValue() <em>Logic Value</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getLogicValue()
	 * @generated
	 * @ordered
	 */
	protected static final LogicValue LOGIC_VALUE_EDEFAULT = LogicValue.TRUE;

	/**
	 * The cached value of the '{@link #getLogicValue() <em>Logic Value</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getLogicValue()
	 * @generated
	 * @ordered
	 */
	protected LogicValue logicValue = LOGIC_VALUE_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected LogicConstantImpl()
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
		return ProblemPackage.Literals.LOGIC_CONSTANT;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public LogicValue getLogicValue()
	{
		return logicValue;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setLogicValue(LogicValue newLogicValue)
	{
		LogicValue oldLogicValue = logicValue;
		logicValue = newLogicValue == null ? LOGIC_VALUE_EDEFAULT : newLogicValue;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.LOGIC_CONSTANT__LOGIC_VALUE, oldLogicValue, logicValue));
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
			case ProblemPackage.LOGIC_CONSTANT__LOGIC_VALUE:
				return getLogicValue();
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
			case ProblemPackage.LOGIC_CONSTANT__LOGIC_VALUE:
				setLogicValue((LogicValue)newValue);
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
			case ProblemPackage.LOGIC_CONSTANT__LOGIC_VALUE:
				setLogicValue(LOGIC_VALUE_EDEFAULT);
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
			case ProblemPackage.LOGIC_CONSTANT__LOGIC_VALUE:
				return logicValue != LOGIC_VALUE_EDEFAULT;
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
		result.append(" (logicValue: ");
		result.append(logicValue);
		result.append(')');
		return result.toString();
	}

} //LogicConstantImpl
