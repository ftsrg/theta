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

import tools.refinery.language.model.problem.ModuleKind;
import tools.refinery.language.model.problem.Node;
import tools.refinery.language.model.problem.Problem;
import tools.refinery.language.model.problem.ProblemPackage;
import tools.refinery.language.model.problem.Statement;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Problem</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * </p>
 * <ul>
 *   <li>{@link tools.refinery.language.model.problem.impl.ProblemImpl#getNodes <em>Nodes</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ProblemImpl#getStatements <em>Statements</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ProblemImpl#getKind <em>Kind</em>}</li>
 *   <li>{@link tools.refinery.language.model.problem.impl.ProblemImpl#isExplicitKind <em>Explicit Kind</em>}</li>
 * </ul>
 *
 * @generated
 */
public class ProblemImpl extends NamedElementImpl implements Problem
{
	/**
	 * The cached value of the '{@link #getNodes() <em>Nodes</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getNodes()
	 * @generated
	 * @ordered
	 */
	protected EList<Node> nodes;

	/**
	 * The cached value of the '{@link #getStatements() <em>Statements</em>}' containment reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getStatements()
	 * @generated
	 * @ordered
	 */
	protected EList<Statement> statements;

	/**
	 * The default value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected static final ModuleKind KIND_EDEFAULT = ModuleKind.PROBLEM;

	/**
	 * The cached value of the '{@link #getKind() <em>Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getKind()
	 * @generated
	 * @ordered
	 */
	protected ModuleKind kind = KIND_EDEFAULT;

	/**
	 * The default value of the '{@link #isExplicitKind() <em>Explicit Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isExplicitKind()
	 * @generated
	 * @ordered
	 */
	protected static final boolean EXPLICIT_KIND_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isExplicitKind() <em>Explicit Kind</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #isExplicitKind()
	 * @generated
	 * @ordered
	 */
	protected boolean explicitKind = EXPLICIT_KIND_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ProblemImpl()
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
		return ProblemPackage.Literals.PROBLEM;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Node> getNodes()
	{
		if (nodes == null)
		{
			nodes = new EObjectContainmentEList<Node>(Node.class, this, ProblemPackage.PROBLEM__NODES);
		}
		return nodes;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Statement> getStatements()
	{
		if (statements == null)
		{
			statements = new EObjectContainmentEList<Statement>(Statement.class, this, ProblemPackage.PROBLEM__STATEMENTS);
		}
		return statements;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ModuleKind getKind()
	{
		return kind;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setKind(ModuleKind newKind)
	{
		ModuleKind oldKind = kind;
		kind = newKind == null ? KIND_EDEFAULT : newKind;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.PROBLEM__KIND, oldKind, kind));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isExplicitKind()
	{
		return explicitKind;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setExplicitKind(boolean newExplicitKind)
	{
		boolean oldExplicitKind = explicitKind;
		explicitKind = newExplicitKind;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProblemPackage.PROBLEM__EXPLICIT_KIND, oldExplicitKind, explicitKind));
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
			case ProblemPackage.PROBLEM__NODES:
				return ((InternalEList<?>)getNodes()).basicRemove(otherEnd, msgs);
			case ProblemPackage.PROBLEM__STATEMENTS:
				return ((InternalEList<?>)getStatements()).basicRemove(otherEnd, msgs);
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
			case ProblemPackage.PROBLEM__NODES:
				return getNodes();
			case ProblemPackage.PROBLEM__STATEMENTS:
				return getStatements();
			case ProblemPackage.PROBLEM__KIND:
				return getKind();
			case ProblemPackage.PROBLEM__EXPLICIT_KIND:
				return isExplicitKind();
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
			case ProblemPackage.PROBLEM__NODES:
				getNodes().clear();
				getNodes().addAll((Collection<? extends Node>)newValue);
				return;
			case ProblemPackage.PROBLEM__STATEMENTS:
				getStatements().clear();
				getStatements().addAll((Collection<? extends Statement>)newValue);
				return;
			case ProblemPackage.PROBLEM__KIND:
				setKind((ModuleKind)newValue);
				return;
			case ProblemPackage.PROBLEM__EXPLICIT_KIND:
				setExplicitKind((Boolean)newValue);
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
			case ProblemPackage.PROBLEM__NODES:
				getNodes().clear();
				return;
			case ProblemPackage.PROBLEM__STATEMENTS:
				getStatements().clear();
				return;
			case ProblemPackage.PROBLEM__KIND:
				setKind(KIND_EDEFAULT);
				return;
			case ProblemPackage.PROBLEM__EXPLICIT_KIND:
				setExplicitKind(EXPLICIT_KIND_EDEFAULT);
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
			case ProblemPackage.PROBLEM__NODES:
				return nodes != null && !nodes.isEmpty();
			case ProblemPackage.PROBLEM__STATEMENTS:
				return statements != null && !statements.isEmpty();
			case ProblemPackage.PROBLEM__KIND:
				return kind != KIND_EDEFAULT;
			case ProblemPackage.PROBLEM__EXPLICIT_KIND:
				return explicitKind != EXPLICIT_KIND_EDEFAULT;
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
		result.append(" (kind: ");
		result.append(kind);
		result.append(", explicitKind: ");
		result.append(explicitKind);
		result.append(')');
		return result.toString();
	}

} //ProblemImpl
