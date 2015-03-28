/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Generic Type</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.GenericType#getBaseType <em>Base Type</em>}</li>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.GenericType#getTypeArguments <em>Type Arguments</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getGenericType()
 * @model
 * @generated
 */
public interface GenericType extends AbstractType {
   /**
    * Returns the value of the '<em><b>Base Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Base Type</em>' reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Base Type</em>' reference.
    * @see #setBaseType(AbstractType)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getGenericType_BaseType()
    * @model
    * @generated
    */
   AbstractType getBaseType();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.GenericType#getBaseType <em>Base Type</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Base Type</em>' reference.
    * @see #getBaseType()
    * @generated
    */
   void setBaseType(AbstractType value);

   /**
    * Returns the value of the '<em><b>Type Arguments</b></em>' reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.AbstractType}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type Arguments</em>' reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type Arguments</em>' reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getGenericType_TypeArguments()
    * @model
    * @generated
    */
   EList<AbstractType> getTypeArguments();

} // GenericType
