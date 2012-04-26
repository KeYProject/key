/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.statistic.ui.adapter;

import java.util.Iterator;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.edit.domain.EditingDomain;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.Viewer;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelEditor;
import de.hentschel.visualdbc.statistic.ui.control.IStatisticProvider;
import de.hentschel.visualdbc.statistic.ui.view.DbcStatisticViewPart;

/**
 * Converts a given {@link DbcmodelEditor} into an {@link IStatisticProvider}.
 * @author Martin Hentschel
 */
public class DbcmodelEditorStatisticAdapterFactory extends AbstractStatisticAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(final Object adaptableObject, @SuppressWarnings("rawtypes") Class adapterType) {
      final IStatisticProvider provider = new IStatisticProvider() {
         private DbcmodelEditor editor;
         
         @Override
         public DbcModel getModel() {
            if (adaptableObject instanceof DbcmodelEditor) {
               editor = (DbcmodelEditor)adaptableObject;
               return searchDbcModel(editor.getEditingDomain());
            }
            else {
               return null;
            }
         }

         @Override
         public void select(ISelection selection) {
            if (editor != null) {
               Viewer viewer = editor.getViewer();
               if (viewer != null) {
                  viewer.setSelection(selection);
               }
            }
         }};
      return new DbcStatisticViewPart(provider);    
   }

   /**
    * Searches the first {@link DbcModel} in the given {@link EditingDomain}.
    * @param editingDomain The given {@link EditingDomain}.
    * @return The first found {@link DbcModel} or {@code null} if no {@link DbcModel} was found.
    */
   protected DbcModel searchDbcModel(EditingDomain editingDomain) {
      DbcModel result = null;
      if (editingDomain != null) {
         ResourceSet rst = editingDomain.getResourceSet();
         if (rst != null) {
            Iterator<Resource> iter = rst.getResources().iterator();
            while (result == null && iter.hasNext()) {
               Resource next = iter.next();
               Iterator<EObject> contentIter = next.getContents().iterator();
               while (result == null && contentIter.hasNext()) {
                  EObject nextObject = contentIter.next();
                  if (nextObject instanceof DbcModel) {
                     result = (DbcModel)nextObject;
                  }
               }
            }
         }
      }
      return result;
   }
}
