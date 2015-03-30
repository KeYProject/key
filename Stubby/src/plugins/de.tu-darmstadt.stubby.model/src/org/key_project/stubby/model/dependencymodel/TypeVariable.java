/**
 */
package org.key_project.stubby.model.dependencymodel;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Type Variable</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.TypeVariable#getType <em>Type</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getTypeVariable()
 * @model
 * @generated
 */
public interface TypeVariable extends AbstractType {
   /**
    * Returns the value of the '<em><b>Type</b></em>' reference.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type</em>' reference isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type</em>' reference.
    * @see #setType(AbstractType)
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getTypeVariable_Type()
    * @model
    * @generated
    */
   AbstractType getType();

   /**
    * Sets the value of the '{@link org.key_project.stubby.model.dependencymodel.TypeVariable#getType <em>Type</em>}' reference.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param value the new value of the '<em>Type</em>' reference.
    * @see #getType()
    * @generated
    */
   void setType(AbstractType value);

} // TypeVariable
