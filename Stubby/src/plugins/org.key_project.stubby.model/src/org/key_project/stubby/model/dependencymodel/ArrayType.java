/**
 */
package org.key_project.stubby.model.dependencymodel;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Array Type</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.ArrayType#getBaseType <em>Base Type</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getArrayType()
 * @model
 * @generated
 */
public interface ArrayType extends AbstractType {
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
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getArrayType_BaseType()
    * @model
    * @generated
    */
   AbstractType getBaseType();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.ArrayType#getBaseType <em>Base Type</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Base Type</em>' reference.
    * @see #getBaseType()
    * @generated
    */
   void setBaseType(AbstractType value);

} // ArrayType
