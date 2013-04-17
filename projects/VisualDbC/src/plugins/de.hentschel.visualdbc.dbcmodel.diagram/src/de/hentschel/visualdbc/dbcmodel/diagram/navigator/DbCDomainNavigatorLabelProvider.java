/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package de.hentschel.visualdbc.dbcmodel.diagram.navigator;

import org.eclipse.emf.edit.ui.provider.AdapterFactoryLabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.navigator.ICommonContentExtensionSite;
import org.eclipse.ui.navigator.ICommonLabelProvider;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;

/**
 * @generated
 */
public class DbCDomainNavigatorLabelProvider implements ICommonLabelProvider {

   /**
    * @generated
    */
   private AdapterFactoryLabelProvider myAdapterFactoryLabelProvider = new AdapterFactoryLabelProvider(
         DbCDiagramEditorPlugin.getInstance().getItemProvidersAdapterFactory());

   /**
    * @generated
    */
   public void init(ICommonContentExtensionSite aConfig) {
   }

   /**
    * @generated
    */
   public Image getImage(Object element) {
      if (element instanceof DbCDomainNavigatorItem) {
         return myAdapterFactoryLabelProvider
               .getImage(((DbCDomainNavigatorItem) element).getEObject());
      }
      return null;
   }

   /**
    * @generated
    */
   public String getText(Object element) {
      if (element instanceof DbCDomainNavigatorItem) {
         return myAdapterFactoryLabelProvider
               .getText(((DbCDomainNavigatorItem) element).getEObject());
      }
      return null;
   }

   /**
    * @generated
    */
   public void addListener(ILabelProviderListener listener) {
      myAdapterFactoryLabelProvider.addListener(listener);
   }

   /**
    * @generated
    */
   public void dispose() {
      myAdapterFactoryLabelProvider.dispose();
   }

   /**
    * @generated
    */
   public boolean isLabelProperty(Object element, String property) {
      return myAdapterFactoryLabelProvider.isLabelProperty(element, property);
   }

   /**
    * @generated
    */
   public void removeListener(ILabelProviderListener listener) {
      myAdapterFactoryLabelProvider.removeListener(listener);
   }

   /**
    * @generated
    */
   public void restoreState(IMemento aMemento) {
   }

   /**
    * @generated
    */
   public void saveState(IMemento aMemento) {
   }

   /**
    * @generated
    */
   public String getDescription(Object anElement) {
      return null;
   }

}