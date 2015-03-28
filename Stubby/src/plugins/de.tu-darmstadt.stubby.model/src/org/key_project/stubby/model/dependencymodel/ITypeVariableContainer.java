/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>IType Variable Container</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.ITypeVariableContainer#getTypeVariables <em>Type Variables</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getITypeVariableContainer()
 * @model interface="true" abstract="true"
 * @generated
 */
public interface ITypeVariableContainer extends EObject {
   /**
    * Returns the value of the '<em><b>Type Variables</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.TypeVariable}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Type Variables</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Type Variables</em>' containment reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getITypeVariableContainer_TypeVariables()
    * @model containment="true"
    * @generated
    */
   EList<TypeVariable> getTypeVariables();

} // ITypeVariableContainer
