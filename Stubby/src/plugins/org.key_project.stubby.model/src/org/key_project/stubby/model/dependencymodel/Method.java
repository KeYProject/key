/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Method</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#isStatic <em>Static</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#isFinal <em>Final</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#isAbstract <em>Abstract</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#getReturnType <em>Return Type</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#getParameterTypes <em>Parameter Types</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#getThrows <em>Throws</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Method#isConstructor <em>Constructor</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod()
 * @model
 * @generated
 */
public interface Method extends ITypeVariableContainer {
   /**
    * Returns the value of the '<em><b>Name</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Name</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Name</em>' attribute.
    * @see #setName(String)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Method#getName <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Name</em>' attribute.
    * @see #getName()
    * @generated
    */
   void setName(String value);

   /**
    * Returns the value of the '<em><b>Visibility</b></em>' attribute.
    * The literals are from the enumeration {@link org.key_project.stubby.model.dependencymodel.Visibility}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Visibility</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Visibility</em>' attribute.
    * @see org.key_project.stubby.model.dependencymodel.Visibility
    * @see #setVisibility(Visibility)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_Visibility()
    * @model
    * @generated
    */
   Visibility getVisibility();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Method#getVisibility <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Visibility</em>' attribute.
    * @see org.key_project.stubby.model.dependencymodel.Visibility
    * @see #getVisibility()
    * @generated
    */
   void setVisibility(Visibility value);

   /**
    * Returns the value of the '<em><b>Static</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Static</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Static</em>' attribute.
    * @see #setStatic(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_Static()
    * @model
    * @generated
    */
   boolean isStatic();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Method#isStatic <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Static</em>' attribute.
    * @see #isStatic()
    * @generated
    */
   void setStatic(boolean value);

   /**
    * Returns the value of the '<em><b>Final</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Final</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Final</em>' attribute.
    * @see #setFinal(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_Final()
    * @model
    * @generated
    */
   boolean isFinal();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Method#isFinal <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Final</em>' attribute.
    * @see #isFinal()
    * @generated
    */
   void setFinal(boolean value);

   /**
    * Returns the value of the '<em><b>Abstract</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Abstract</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Abstract</em>' attribute.
    * @see #setAbstract(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_Abstract()
    * @model
    * @generated
    */
   boolean isAbstract();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Method#isAbstract <em>Abstract</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Abstract</em>' attribute.
    * @see #isAbstract()
    * @generated
    */
   void setAbstract(boolean value);

   /**
    * Returns the value of the '<em><b>Return Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Return Type</em>' reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Return Type</em>' reference.
    * @see #setReturnType(AbstractType)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_ReturnType()
    * @model
    * @generated
    */
   AbstractType getReturnType();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Method#getReturnType <em>Return Type</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Return Type</em>' reference.
    * @see #getReturnType()
    * @generated
    */
   void setReturnType(AbstractType value);

   /**
    * Returns the value of the '<em><b>Parameter Types</b></em>' reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.AbstractType}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Parameter Types</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Parameter Types</em>' reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_ParameterTypes()
    * @model
    * @generated
    */
   EList<AbstractType> getParameterTypes();

   /**
    * Returns the value of the '<em><b>Throws</b></em>' reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.AbstractType}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Throws</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Throws</em>' reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_Throws()
    * @model
    * @generated
    */
   EList<AbstractType> getThrows();

   /**
    * Returns the value of the '<em><b>Constructor</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Constructor</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Constructor</em>' attribute.
    * @see #setConstructor(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getMethod_Constructor()
    * @model
    * @generated
    */
   boolean isConstructor();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Method#isConstructor <em>Constructor</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Constructor</em>' attribute.
    * @see #isConstructor()
    * @generated
    */
   void setConstructor(boolean value);

} // Method
