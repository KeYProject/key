/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package org.key_project.sed.ui.visualization.model.od.util;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;

import org.eclipse.emf.common.notify.impl.AdapterFactoryImpl;

import org.eclipse.emf.ecore.EObject;

import org.key_project.sed.ui.visualization.model.od.*;

/**
 * <!-- begin-user-doc -->
 * The <b>Adapter Factory</b> for the model.
 * It provides an adapter <code>createXXX</code> method for each class of the model.
 * <!-- end-user-doc -->
 * @see org.key_project.sed.ui.visualization.model.od.ODPackage
 * @generated
 */
public class ODAdapterFactory extends AdapterFactoryImpl {
   /**
    * The cached model package.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected static ODPackage modelPackage;

   /**
    * Creates an instance of the adapter factory.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public ODAdapterFactory() {
      if (modelPackage == null) {
         modelPackage = ODPackage.eINSTANCE;
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
   protected ODSwitch<Adapter> modelSwitch =
      new ODSwitch<Adapter>() {
         @Override
         public Adapter caseODObject(ODObject object) {
            return createODObjectAdapter();
         }
         @Override
         public Adapter caseODValue(ODValue object) {
            return createODValueAdapter();
         }
         @Override
         public Adapter caseODModel(ODModel object) {
            return createODModelAdapter();
         }
         @Override
         public Adapter caseODAssociation(ODAssociation object) {
            return createODAssociationAdapter();
         }
         @Override
         public Adapter caseODState(ODState object) {
            return createODStateAdapter();
         }
         @Override
         public Adapter caseAbstractODValueContainer(AbstractODValueContainer object) {
            return createAbstractODValueContainerAdapter();
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
    * Creates a new adapter for an object of class '{@link org.key_project.sed.ui.visualization.model.od.ODObject <em>Object</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.sed.ui.visualization.model.od.ODObject
    * @generated
    */
   public Adapter createODObjectAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.sed.ui.visualization.model.od.ODValue <em>Value</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.sed.ui.visualization.model.od.ODValue
    * @generated
    */
   public Adapter createODValueAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.sed.ui.visualization.model.od.ODModel <em>Model</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.sed.ui.visualization.model.od.ODModel
    * @generated
    */
   public Adapter createODModelAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.sed.ui.visualization.model.od.ODAssociation <em>Association</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.sed.ui.visualization.model.od.ODAssociation
    * @generated
    */
   public Adapter createODAssociationAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.sed.ui.visualization.model.od.ODState <em>State</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.sed.ui.visualization.model.od.ODState
    * @generated
    */
   public Adapter createODStateAdapter() {
      return null;
   }

   /**
    * Creates a new adapter for an object of class '{@link org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer <em>Abstract OD Value Container</em>}'.
    * <!-- begin-user-doc -->
    * This default implementation returns null so that we can easily ignore cases;
    * it's useful to ignore a case when inheritance will catch all the cases anyway.
    * <!-- end-user-doc -->
    * @return the new adapter.
    * @see org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer
    * @generated
    */
   public Adapter createAbstractODValueContainerAdapter() {
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

} //ODAdapterFactory