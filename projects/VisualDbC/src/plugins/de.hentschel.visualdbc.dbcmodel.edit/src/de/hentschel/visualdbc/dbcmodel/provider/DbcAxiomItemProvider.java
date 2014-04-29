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


import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;

import java.util.Collection;
import java.util.List;

import org.eclipse.emf.common.notify.AdapterFactory;
import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.common.util.ResourceLocator;

import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.edit.provider.ComposeableAdapterFactory;
import org.eclipse.emf.edit.provider.IEditingDomainItemProvider;
import org.eclipse.emf.edit.provider.IItemLabelProvider;
import org.eclipse.emf.edit.provider.IItemPropertyDescriptor;
import org.eclipse.emf.edit.provider.IItemPropertySource;
import org.eclipse.emf.edit.provider.IStructuredItemContentProvider;
import org.eclipse.emf.edit.provider.ITreeItemContentProvider;
import org.eclipse.emf.edit.provider.ItemPropertyDescriptor;
import org.eclipse.emf.edit.provider.ItemProviderAdapter;
import org.eclipse.emf.edit.provider.ViewerNotification;

/**
 * This is the item provider adapter for a {@link de.hentschel.visualdbc.dbcmodel.DbcAxiom} object.
 * <!-- begin-user-doc -->
 * <!-- end-user-doc -->
 * @generated
 */
public class DbcAxiomItemProvider
    extends ItemProviderAdapter
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
    public DbcAxiomItemProvider(AdapterFactory adapterFactory) {
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

         addNamePropertyDescriptor(object);
         addDefinitionPropertyDescriptor(object);
      }
      return itemPropertyDescriptors;
   }

    /**
    * This adds a property descriptor for the Name feature.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    protected void addNamePropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_AbstractDbcSpecification_name_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_AbstractDbcSpecification_name_feature", "_UI_AbstractDbcSpecification_type"),
             DbcmodelPackage.Literals.ABSTRACT_DBC_SPECIFICATION__NAME,
             true,
             false,
             false,
             ItemPropertyDescriptor.GENERIC_VALUE_IMAGE,
             null,
             null));
   }

    /**
    * This adds a property descriptor for the Definition feature.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    protected void addDefinitionPropertyDescriptor(Object object) {
      itemPropertyDescriptors.add
         (createItemPropertyDescriptor
            (((ComposeableAdapterFactory)adapterFactory).getRootAdapterFactory(),
             getResourceLocator(),
             getString("_UI_DbcAxiom_definition_feature"),
             getString("_UI_PropertyDescriptor_description", "_UI_DbcAxiom_definition_feature", "_UI_DbcAxiom_type"),
             DbcmodelPackage.Literals.DBC_AXIOM__DEFINITION,
             true,
             true,
             false,
             ItemPropertyDescriptor.GENERIC_VALUE_IMAGE,
             null,
             null));
   }

    /**
    * This specifies how to implement {@link #getChildren} and is used to deduce an appropriate feature for an
    * {@link org.eclipse.emf.edit.command.AddCommand}, {@link org.eclipse.emf.edit.command.RemoveCommand} or
    * {@link org.eclipse.emf.edit.command.MoveCommand} in {@link #createCommand}.
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   public Collection<? extends EStructuralFeature> getChildrenFeatures(Object object) {
      if (childrenFeatures == null) {
         super.getChildrenFeatures(object);
         childrenFeatures.add(DbcmodelPackage.Literals.DBC_AXIOM__AXIOM_CONTRACTS);
      }
      return childrenFeatures;
   }

   /**
    * <!-- begin-user-doc -->
    * <!-- end-user-doc -->
    * @generated
    */
   @Override
   protected EStructuralFeature getChildFeature(Object object, Object child) {
      // Check the type of the specified child object and return the proper feature to use for
      // adding (see {@link AddCommand}) it as a child.

      return super.getChildFeature(object, child);
   }

   /**
    * This returns DbcAxiom.gif.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    @Override
    public Object getImage(Object object) {
      return overlayImage(object, getResourceLocator().getImage("full/obj16/DbcAxiom"));
   }

    /**
    * This returns the label text for the adapted class.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    @Override
    public String getText(Object object) {
      String label = ((DbcAxiom)object).getName();
      return label == null || label.length() == 0 ?
         getString("_UI_DbcAxiom_type") :
         getString("_UI_DbcAxiom_type") + " " + label;
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

      switch (notification.getFeatureID(DbcAxiom.class)) {
         case DbcmodelPackage.DBC_AXIOM__NAME:
         case DbcmodelPackage.DBC_AXIOM__DEFINITION:
            fireNotifyChanged(new ViewerNotification(notification, notification.getNotifier(), false, true));
            return;
         case DbcmodelPackage.DBC_AXIOM__AXIOM_CONTRACTS:
            fireNotifyChanged(new ViewerNotification(notification, notification.getNotifier(), true, false));
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

      newChildDescriptors.add
         (createChildParameter
            (DbcmodelPackage.Literals.DBC_AXIOM__AXIOM_CONTRACTS,
             DbcmodelFactory.eINSTANCE.createDbCAxiomContract()));
   }

    /**
    * Return the resource locator for this item provider's resources.
    * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
    * @generated
    */
    @Override
    public ResourceLocator getResourceLocator() {
      return DbCEditPlugin.INSTANCE;
   }

}