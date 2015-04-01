/**
 */
package org.key_project.stubby.model.dependencymodel;

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage
 * @generated
 */
public interface DependencymodelFactory extends EFactory {
   /**
    * The singleton instance of the factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   DependencymodelFactory eINSTANCE = org.key_project.stubby.model.dependencymodel.impl.DependencymodelFactoryImpl.init();

   /**
    * Returns a new object of class '<em>Type</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Type</em>'.
    * @generated
    */
   Type createType();

   /**
    * Returns a new object of class '<em>Method</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Method</em>'.
    * @generated
    */
   Method createMethod();

   /**
    * Returns a new object of class '<em>Field</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Field</em>'.
    * @generated
    */
   Field createField();

   /**
    * Returns a new object of class '<em>Dependency Model</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Dependency Model</em>'.
    * @generated
    */
   DependencyModel createDependencyModel();

   /**
    * Returns a new object of class '<em>Type Variable</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Type Variable</em>'.
    * @generated
    */
   TypeVariable createTypeVariable();

   /**
    * Returns a new object of class '<em>Type Usage</em>'.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return a new object of class '<em>Type Usage</em>'.
    * @generated
    */
   TypeUsage createTypeUsage();

   /**
    * Returns the package supported by this factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the package supported by this factory.
    * @generated
    */
   DependencymodelPackage getDependencymodelPackage();

} //DependencymodelFactory
