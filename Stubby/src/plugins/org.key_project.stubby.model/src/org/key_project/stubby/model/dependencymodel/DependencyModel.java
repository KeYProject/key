/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Dependency Model</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.key_project.stubby.model.dependencymodel.DependencyModel#getTypes <em>Types</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getDependencyModel()
 * @model
 * @generated
 */
public interface DependencyModel extends EObject {
   /**
    * Returns the value of the '<em><b>Types</b></em>' containment reference list.
    * The list contents are of type {@link org.key_project.stubby.model.dependencymodel.Type}.
    * <!-- begin-user-doc -->
    * <p>
    * If the meaning of the '<em>Types</em>' containment reference list isn't clear,
    * there really should be more of a description here...
    * </p>
    * <!-- end-user-doc -->
    * @return the value of the '<em>Types</em>' containment reference list.
    * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage#getDependencyModel_Types()
    * @model containment="true"
    * @generated
    */
   EList<Type> getTypes();

} // DependencyModel
