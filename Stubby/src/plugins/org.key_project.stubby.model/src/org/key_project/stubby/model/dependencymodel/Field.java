/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Field</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Field#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Field#getVisibility <em>Visibility</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Field#isFinal <em>Final</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Field#isStatic <em>Static</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Field#getConstantValue <em>Constant Value</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.Field#getType <em>Type</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getField()
 * @model
 * @generated
 */
public interface Field extends EObject {
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
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getField_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Field#getName <em>Name</em>}' attribute.
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
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getField_Visibility()
    * @model
    * @generated
    */
   Visibility getVisibility();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Field#getVisibility <em>Visibility</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Visibility</em>' attribute.
    * @see org.key_project.stubby.model.dependencymodel.Visibility
    * @see #getVisibility()
    * @generated
    */
   void setVisibility(Visibility value);

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
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getField_Final()
    * @model
    * @generated
    */
   boolean isFinal();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Field#isFinal <em>Final</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Final</em>' attribute.
    * @see #isFinal()
    * @generated
    */
   void setFinal(boolean value);

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
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getField_Static()
    * @model
    * @generated
    */
   boolean isStatic();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Field#isStatic <em>Static</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Static</em>' attribute.
    * @see #isStatic()
    * @generated
    */
   void setStatic(boolean value);

   /**
    * Returns the value of the '<em><b>Constant Value</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Constant Value</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Constant Value</em>' attribute.
    * @see #setConstantValue(String)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getField_ConstantValue()
    * @model
    * @generated
    */
   String getConstantValue();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Field#getConstantValue <em>Constant Value</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Constant Value</em>' attribute.
    * @see #getConstantValue()
    * @generated
    */
   void setConstantValue(String value);

   /**
    * Returns the value of the '<em><b>Type</b></em>' containment reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type</em>' containment reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type</em>' containment reference.
    * @see #setType(TypeUsage)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getField_Type()
    * @model containment="true"
    * @generated
    */
   TypeUsage getType();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.Field#getType <em>Type</em>}' containment reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Type</em>' containment reference.
    * @see #getType()
    * @generated
    */
   void setType(TypeUsage value);

} // Field
