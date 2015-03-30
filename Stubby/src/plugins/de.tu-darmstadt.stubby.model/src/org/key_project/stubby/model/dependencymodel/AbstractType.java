/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Abstract Type</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.AbstractType#getName <em>Name</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.AbstractType#isSource <em>Source</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getAbstractType()
 * @model abstract="true"
 * @generated
 */
public interface AbstractType extends EObject {
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
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getAbstractType_Name()
    * @model
    * @generated
    */
   String getName();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.AbstractType#getName <em>Name</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Name</em>' attribute.
    * @see #getName()
    * @generated
    */
   void setName(String value);

   /**
    * Returns the value of the '<em><b>Source</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Source</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Source</em>' attribute.
    * @see #setSource(boolean)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getAbstractType_Source()
    * @model
    * @generated
    */
   boolean isSource();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.AbstractType#isSource <em>Source</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Source</em>' attribute.
    * @see #isSource()
    * @generated
    */
   void setSource(boolean value);

} // AbstractType
