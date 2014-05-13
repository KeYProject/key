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
package de.hentschel.visualdbc.dbcmodel.provider;


import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

import java.util.Collection;
import java.util.List;

import org.eclipse.emf.common.notify.AdapterFactory;
import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.edit.provider.ComposeableAdapterFactory;
import org.eclipse.emf.edit.provider.IEditingDomainItemProvider;
import org.eclipse.emf.edit.provider.IItemLabelProvider;
import org.eclipse.emf.edit.provider.IItemPropertyDescriptor;
import org.eclipse.emf.edit.provider.IItemPropertySource;
import org.eclipse.emf.edit.provider.IStructuredItemContentProvider;
import org.eclipse.emf.edit.provider.ITreeItemContentProvider;
import org.eclipse.emf.edit.provider.ItemPropertyDescriptor;
import org.eclipse.emf.edit.provider.ViewerNotification;

/**
 * This is the item provider adapter for a {@link de.hentschel.visualdbc.dbcmodel.DbcOperationContract} object.
 * <!-- begin-user-doc -->
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcOperationContractItemProvider
   extends AbstractDbcSpecificationItemProvider
   implements
      IEditingDomainItemProvider,
      IStructuredItemContentProvider,
      ITreeItemContentProvider,
      IItemLabelProvider,
      IItemPropertySource {
   /**
    * This constructs an instance from a factory and a notifier.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   public DbcOperationContractItemProvider(AdapterFactory adapterFactory) {
      super(adapterFactory);
   }

   /**
    * This returns the property descriptors for the adapted class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public List<IItemPropertyDescriptor> getPropertyDescriptors(Object object) {
      if (itemPropertyDescriptors == null) {
         super.getPropertyDescriptors(object);

         addProofObligationsPropertyDescriptor(object);
         addPrePropertyDescriptor(object);
         addPostPropertyDescriptor(object);
         addModifiesPropertyDescriptor(object);
         addTerminationPropertyDescriptor(object);
      }
      return itemPropertyDescriptors;
   }

   /**
    * This adds a property descriptor for the Proof Obligations feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addProofObligationsPropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_IDbCProvable_proofObligations_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_IDbCProvable_proofObligations_feature", "_UI_IDbCProvable_type"),
             DbcmodelPackage.Literals.IDB_CPROVABLE__PROOF_OBLIGATIONS,
             true,
             false,
             true,
             null,
             null,
             null));
   }

   /**
    * This adds a property descriptor for the Pre feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addPrePropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcOperationContract_pre_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcOperationContract_pre_feature", "_UI_DbcOperationContract_type"),
             DbcmodelPackage.Literals.DBC_OPERATION_CONTRACT__PRE,
             true,
             true,
             false,
             ItemPropertyDescriptor.GENERIC_VALUE_IMAGE,
             null,
             null));
   }

   /**
    * This adds a property descriptor for the Post feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addPostPropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcOperationContract_post_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcOperationContract_post_feature", "_UI_DbcOperationContract_type"),
             DbcmodelPackage.Literals.DBC_OPERATION_CONTRACT__POST,
             true,
             true,
             false,
             ItemPropertyDescriptor.GENERIC_VALUE_IMAGE,
             null,
             null));
   }

   /**
    * This adds a property descriptor for the Modifies feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addModifiesPropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcOperationContract_modifies_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcOperationContract_modifies_feature", "_UI_DbcOperationContract_type"),
             DbcmodelPackage.Literals.DBC_OPERATION_CONTRACT__MODIFIES,
             true,
             false,
             false,
             ItemPropertyDescriptor.GENERIC_VALUE_IMAGE,
             null,
             null));
   }

   /**
    * This adds a property descriptor for the Termination feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addTerminationPropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcOperationContract_termination_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcOperationContract_termination_feature", "_UI_DbcOperationContract_type"),
             DbcmodelPackage.Literals.DBC_OPERATION_CONTRACT__TERMINATION,
             true,
             false,
             false,
             ItemPropertyDescriptor.GENERIC_VALUE_IMAGE,
             null,
             null));
   }

   /**
    * This returns DbcOperationContract.gif.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   @Override
   public Object getImage(Object object) {
      // Begin Changes MHE
      String imagePath = "full/obj16/DbcOperationContract";
      if (object instanceof DbcOperationContract) {
         DbcOperationContract contract = (DbcOperationContract)object;
         if ("box".equals(contract.getTermination())) {
            imagePath = "full/obj16/DbcOperationContract_Box";
         }
         else if ("diamond".equals(contract.getTermination())) {
            imagePath = "full/obj16/DbcOperationContract_Diamond";
         }
      }
      return overlayImage(object, getResourceLocator().getImage(imagePath));
      // End Changes MHE      
   }

   /**
    * This returns the label text for the adapted class.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public String getText(Object object) {
      String label = ((DbcOperationContract)object).getName();
      return label == null || label.length() == 0 ?
         getString("_UI_DbcOperationContract_type") :
         getString("_UI_DbcOperationContract_type") + " " + label;
   }

   /**
    * This handles model notifications by calling {@link #updateChildren} to update any cached
    * children and by creating a viewer notification, which it passes to {@link #fireNotifyChanged}.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public void notifyChanged(Notification notification) {
      updateChildren(notification);

      switch (notification.getFeatureID(DbcOperationContract.class)) {
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__PRE:
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__POST:
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__MODIFIES:
         case DbcmodelPackage.DBC_OPERATION_CONTRACT__TERMINATION:
            fireNotifyChanged(new ViewerNotification(notification, notification.getNotifier(), false, true));
            return;
      }
      super.notifyChanged(notification);
   }

   /**
    * This adds {@link org.eclipse.emf.edit.command.CommandParameter}s describing the children
    * that can be created under this object.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected void collectNewChildDescriptors(Collection<Object> newChildDescriptors, Object object) {
      super.collectNewChildDescriptors(newChildDescriptors, object);
   }

}