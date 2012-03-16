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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.gef.EditPart;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.statistic.ui.control.IStatisticProvider;
import de.hentschel.visualdbc.statistic.ui.view.DbcStatisticViewPart;

/**
 * Converts a given {@link DbCDiagramEditor} into an {@link IStatisticProvider}.
 * @author Martin Hentschel
 */
public class DbCDiagramEditorStatisticAdapterFactory extends AbstractStatisticAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(final Object adaptableObject, @SuppressWarnings("rawtypes") Class adapterType) {
      final IStatisticProvider provider = new IStatisticProvider() {
         private DbCDiagramEditor editor;
         
         @Override
         public DbcModel getModel() {
            if (adaptableObject instanceof DbCDiagramEditor) {
               editor = (DbCDiagramEditor)adaptableObject;
               return (DbcModel)editor.getDiagram().getElement();
            }
            else {
               return null;
            }
         }

         @Override
         public void select(ISelection selection) {
            if (editor != null) {
               if (selection instanceof IStructuredSelection) {
                  Object[] elements = ((IStructuredSelection)selection).toArray();
                  List<EditPart> parts = new LinkedList<EditPart>();
                  // Find EditParts for the contained EObjects
                  for (Object element : elements) {
                     if (element instanceof EObject) {
                        EditPart part = editor.getDiagramEditPart().findEditPart(editor.getDiagramEditPart(), (EObject)element);
                        if (part != null) {
                           editor.getDiagramGraphicalViewer().reveal(part); // Make EditPart visible
                           parts.add(part);
                        }
                     }
                  }
                  // Select EditParts
                  editor.getDiagramGraphicalViewer().setSelection(new StructuredSelection(parts));
               }
            }
         }};
         return new DbcStatisticViewPart(provider);
   }
}
