/**
 */
package org.key_project.stubby.model.dependencymodel.util;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.util.Switch;

import org.key_project.stubby.model.dependencymodel.*;

/**
 * <!-- begin-user-doc -->
 * The <b>Switch</b> for the model's inheritance hierarchy.
 * It supports the call {@link #doSwitch(EObject) doSwitch(object)}
 * to invoke the <code>caseXXX</code> method for each class of the model,
 * starting with the actual class of the object
 * and proceeding up the inheritance hierarchy
 * until a non-null result is returned,
 * which is the result of the switch.
 * <!-- end-user-doc -->
 * @see org.key_project.stubby.model.dependencymodel.DependencymodelPackage
 * @generated
 */
public class DependencymodelSwitch<T> extends Switch<T> {
   /**
    * The cached model package
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected static DependencymodelPackage modelPackage;

   /**
    * Creates an instance of the switch.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DependencymodelSwitch() {
      if (modelPackage == null) {
         modelPackage = DependencymodelPackage.eINSTANCE;
      }
   }

   /**
    * Checks whether this is a switch for the given package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @parameter ePackage the package in question.
    * @return whether this is a switch for the given package.
    * @generated
    */
   @Override
   protected boolean isSwitchFor(EPackage ePackage) {
      return ePackage == modelPackage;
   }

   /**
    * Calls <code>caseXXX</code> for each class of the model until one returns a non null result; it yields that result.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @return the first non-null result returned by a <code>caseXXX</code> call.
    * @generated
    */
   @Override
   protected T doSwitch(int classifierID, EObject theEObject) {
      switch (classifierID) {
         case DependencymodelPackage.TYPE: {
            Type type = (Type)theEObject;
            T result = caseType(type);
            if (result == null) result = caseAbstractType(type);
            if (result == null) result = caseITypeVariableContainer(type);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.METHOD: {
            Method method = (Method)theEObject;
            T result = caseMethod(method);
            if (result == null) result = caseITypeVariableContainer(method);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.FIELD: {
            Field field = (Field)theEObject;
            T result = caseField(field);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.DEPENDENCY_MODEL: {
            DependencyModel dependencyModel = (DependencyModel)theEObject;
            T result = caseDependencyModel(dependencyModel);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.ABSTRACT_TYPE: {
            AbstractType abstractType = (AbstractType)theEObject;
            T result = caseAbstractType(abstractType);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.ARRAY_TYPE: {
            ArrayType arrayType = (ArrayType)theEObject;
            T result = caseArrayType(arrayType);
            if (result == null) result = caseAbstractType(arrayType);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.DATATYPE: {
            Datatype datatype = (Datatype)theEObject;
            T result = caseDatatype(datatype);
            if (result == null) result = caseAbstractType(datatype);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.GENERIC_TYPE: {
            GenericType genericType = (GenericType)theEObject;
            T result = caseGenericType(genericType);
            if (result == null) result = caseAbstractType(genericType);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.TYPE_VARIABLE: {
            TypeVariable typeVariable = (TypeVariable)theEObject;
            T result = caseTypeVariable(typeVariable);
            if (result == null) result = caseAbstractType(typeVariable);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.WILDCARD_TYPE: {
            WildcardType wildcardType = (WildcardType)theEObject;
            T result = caseWildcardType(wildcardType);
            if (result == null) result = caseAbstractType(wildcardType);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         case DependencymodelPackage.ITYPE_VARIABLE_CONTAINER: {
            ITypeVariableContainer iTypeVariableContainer = (ITypeVariableContainer)theEObject;
            T result = caseITypeVariableContainer(iTypeVariableContainer);
            if (result == null) result = defaultCase(theEObject);
            return result;
         }
         default: return defaultCase(theEObject);
      }
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Type</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Type</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseType(Type object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Method</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Method</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseMethod(Method object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Field</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Field</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseField(Field object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Dependency Model</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Dependency Model</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDependencyModel(DependencyModel object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Abstract Type</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Abstract Type</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseAbstractType(AbstractType object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Array Type</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Array Type</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseArrayType(ArrayType object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Datatype</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Datatype</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseDatatype(Datatype object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Generic Type</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Generic Type</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseGenericType(GenericType object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Type Variable</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Type Variable</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseTypeVariable(TypeVariable object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>Wildcard Type</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>Wildcard Type</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseWildcardType(WildcardType object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>IType Variable Container</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>IType Variable Container</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject) doSwitch(EObject)
    * @generated
    */
   public T caseITypeVariableContainer(ITypeVariableContainer object) {
      return null;
   }

   /**
    * Returns the result of interpreting the object as an instance of '<em>EObject</em>'.
    * <!-- begin-user-doc -->
    * This implementation returns null;
    * returning a non-null result will terminate the switch, but this is the last case anyway.
    * <!-- end-user-doc -->
    * @param object the target of the switch.
    * @return the result of interpreting the object as an instance of '<em>EObject</em>'.
    * @see #doSwitch(org.eclipse.emf.ecore.EObject)
    * @generated
    */
   @Override
   public T defaultCase(EObject object) {
      return null;
   }

} //DependencymodelSwitch
