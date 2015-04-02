/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Type Usage</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.TypeUsage#getType <em>Type</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.TypeUsage#getGenericFreeType <em>Generic Free Type</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getTypeUsage()
 * @model
 * @generated
 */
public interface TypeUsage extends EObject {
   /**
    * Returns the value of the '<em><b>Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type</em>' attribute.
    * @see #setType(String)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getTypeUsage_Type()
    * @model
    * @generated
    */
   String getType();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.TypeUsage#getType <em>Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Type</em>' attribute.
    * @see #getType()
    * @generated
    */
   void setType(String value);

   /**
    * Returns the value of the '<em><b>Generic Free Type</b></em>' attribute.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Generic Free Type</em>' attribute isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Generic Free Type</em>' attribute.
    * @see #setGenericFreeType(String)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getTypeUsage_GenericFreeType()
    * @model
    * @generated
    */
   String getGenericFreeType();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.TypeUsage#getGenericFreeType <em>Generic Free Type</em>}' attribute.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Generic Free Type</em>' attribute.
    * @see #getGenericFreeType()
    * @generated
    */
   void setGenericFreeType(String value);

} // TypeUsage
