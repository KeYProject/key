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

import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

/**
 * This is the item provider adapter for a {@link de.hentschel.visualdbc.dbcmodel.DbcMethod} object.
 * <!-- begin-user-doc -->
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcMethodItemProvider
   extends AbstractDbcOperationItemProvider
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
   public DbcMethodItemProvider(AdapterFactory adapterFactory) {
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

         addReturnTypePropertyDescriptor(object);
         addAbstractPropertyDescriptor(object);
         addFinalPropertyDescriptor(object);
      }
      return itemPropertyDescriptors;
   }

   /**
    * This adds a property descriptor for the Return Type feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addReturnTypePropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcMethod_returnType_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcMethod_returnType_feature", "_UI_DbcMethod_type"),
             DbcmodelPackage.Literals.DBC_METHOD__RETURN_TYPE,
             true,
             false,
             false,
             ItemPropertyDescriptor.GENERIC_VALUE_IMAGE,
             null,
             null));
   }

   /**
    * This adds a property descriptor for the Abstract feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addAbstractPropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcMethod_abstract_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcMethod_abstract_feature", "_UI_DbcMethod_type"),
             DbcmodelPackage.Literals.DBC_METHOD__ABSTRACT,
             true,
             false,
             false,
             ItemPropertyDescriptor.BOOLEAN_VALUE_IMAGE,
             null,
             null));
   }

   /**
    * This adds a property descriptor for the Final feature.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   protected void addFinalPropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcMethod_final_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcMethod_final_feature", "_UI_DbcMethod_type"),
             DbcmodelPackage.Literals.DBC_METHOD__FINAL,
             true,
             false,
             false,
             ItemPropertyDescriptor.BOOLEAN_VALUE_IMAGE,
             null,
             null));
   }

   /**
    * This returns DbcMethod.gif.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated NOT
    */
   @Override
   public Object getImage(Object object) {
      // Begin Changes MHE
      String imagePath = "full/obj16/DbcMethod";
      if (object instanceof DbcMethod) {
         DbcMethod method = (DbcMethod)object;
         switch (method.getVisibility()) {
            case PRIVATE : imagePath = "full/obj16/methpri_obj";
                           break;
            case PROTECTED : imagePath = "full/obj16/methpro_obj";
                             break;
            case PUBLIC : imagePath = "full/obj16/methpub_obj";
                          break;
            default : imagePath = "full/obj16/methdef_obj";
                      break;
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
      String label = ((DbcMethod)object).getSignature();
      return label == null || label.length() == 0 ?
         getString("_UI_DbcMethod_type") :
         getString("_UI_DbcMethod_type") + " " + label;
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

      switch (notification.getFeatureID(DbcMethod.class)) {
         case DbcmodelPackage.DBC_METHOD__RETURN_TYPE:
         case DbcmodelPackage.DBC_METHOD__ABSTRACT:
         case DbcmodelPackage.DBC_METHOD__FINAL:
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