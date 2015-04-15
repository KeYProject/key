/**
 */
package org.key_project.stubby.model.dependencymodel.util;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;

import org.eclipse.emf.common.notify.impl.AdapterFactoryImpl;

import org.eclipse.emf.ecore.EObject;

import org.key_project.stubby.model.dependencymodel.*;

/**
 * <!-- begin-user-doc -->
 * The <b>Adapter Factory</b> for the model.
 * It provides an adapter <code>createXXX</code> method for each class of the model.
 * <!-- end-user-doc -->
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage
 * @generated
 */
public class DependencymodelAdapterFactory extends AdapterFactoryImpl {
   /**
    * The cached model package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected static DependencymodelPackage modelPackage;

   /**
    * Creates an instance of the adapter factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DependencymodelAdapterFactory() {
      if (modelPackage == null) {
         modelPackage = DependencymodelPackage.eINSTANCE;
      }
   }

   /**
    * Returns whether this factory is applicable for the type of the object.
    * <!-- begin-user-doc -->
    * This implementation returns <code>true</code> if the object is either the model's package or is an instance object of the model.
    * <!-- end-user-doc -->
    * @return whether this factory is applicable for the type of the object.
    * @generated
    */
   @Override
   public boolean isFactoryForType(Object object) {
      if (object == modelPackage) {
         return true;
      }
      if (object instanceof EObject) {
         return ((EObject)object).eClass().getEPackage() == modelPackage;
      }
      return false;
   }

   /**
    * The switch that delegates to the <code>createXXX</code> methods.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected DependencymodelSwitch<Adapter> modelSwitch =
      new DependencymodelSwitch<Adapter>() {
         @Override
         public Adapter caseType(Type object) {
            return createTypeAdapter();
         }
         @Override
         public Adapter caseMethod(Method object) {
            return createMethodAdapter();
         }
         @Override
         public Adapter caseField(Field object) {
            return createFieldAdapter();
         }
         @Override
         public Adapter caseDependencyModel(DependencyModel object) {
            return createDependencyModelAdapter();
         }
         @Override
         public Adapter caseTypeVariable(TypeVariable object) {
            return createTypeVariableAdapter();
         }
         @Override
         public Adapter caseITypeVariableContainer(ITypeVariableContainer object) {
            return createITypeVariableContainerAdapter();
         }
         @Override
         public Adapter caseTypeUsage(TypeUsage object) {
            return createTypeUsageAdapter();
         }
         @Override
         public Adapter defaultCase(EObject object) {
            return createEObjectAdapter();
         }
      };

   /**
    * Creates an adapter for the <code>target</code>.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @param target the object to adapt.
    * @return the adapter for the <code>target</code>.
    * @generated
    */
   @Override
   public Adapter createAdapter(Notifier target) {
      return modelSwitch.doSwitch((EObject)target);
   }


   /**
    * Creates a new adapter for an object of class '{@link org.key_project.stubby.model.dependencymodel.Type <em>Type</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.stubby.model.dependencymodel.Type
    * @generated
    */
   public Adapter createTypeAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.stubby.model.dependencymodel.Method <em>Method</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.stubby.model.dependencymodel.Method
    * @generated
    */
   public Adapter createMethodAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.stubby.model.dependencymodel.Field <em>Field</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.stubby.model.dependencymodel.Field
    * @generated
    */
   public Adapter createFieldAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.stubby.model.dependencymodel.DependencyModel <em>Dependency Model</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.stubby.model.dependencymodel.DependencyModel
    * @generated
    */
   public Adapter createDependencyModelAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.stubby.model.dependencymodel.TypeVariable <em>Type Variable</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.stubby.model.dependencymodel.TypeVariable
    * @generated
    */
   public Adapter createTypeVariableAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.stubby.model.dependencymodel.ITypeVariableContainer <em>IType Variable Container</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.stubby.model.dependencymodel.ITypeVariableContainer
    * @generated
    */
   public Adapter createITypeVariableContainerAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.stubby.model.dependencymodel.TypeUsage <em>Type Usage</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.stubby.model.dependencymodel.TypeUsage
    * @generated
    */
   public Adapter createTypeUsageAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for the default case.
    * <!-- begin-user-doc -->
    * This default implementation returns null.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @generated
    */
   public Adapter createEObjectAdapter() {
      return null;
   }

} //DependencymodelAdapterFactory
