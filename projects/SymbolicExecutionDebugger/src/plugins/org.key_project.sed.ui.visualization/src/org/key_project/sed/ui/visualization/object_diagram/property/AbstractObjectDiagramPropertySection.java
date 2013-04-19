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

package org.key_project.sed.ui.visualization.object_diagram.property;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.eclipse.graphiti.ui.platform.GFPropertySection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.sed.ui.visualization.model.od.ODObject;

/**
 * Provides a basic implementation of {@link GFPropertySection} used for property tab of object diagrams.
 * @author Martin Hentschel
 */
public abstract class AbstractObjectDiagramPropertySection<T> extends GFPropertySection {
   /**
    * Returns the {@link ODObject} to show.
    * @return The {@link ODObject} to show or {@code null} if no one should be shown.
    */
   public T getBusinessObject() {
      return getBusinessObject(getSelectedPictogramElement());
   }
   
   /**
    * Returns the {@link ODObject} to show.
    * @param pe The currently selected {@link PictogramElement}.
    * @return The {@link ODObject} to show or {@code null} if no one should be shown.
    */
   @SuppressWarnings("unchecked")
   public T getBusinessObject(PictogramElement pe) {
      T result = null;
      if (pe != null) {
         IDiagramTypeProvider diagramProvider = getDiagramTypeProvider();
         if (diagramProvider != null) {
            IFeatureProvider featureProvider = diagramProvider.getFeatureProvider();
            if (featureProvider != null) {
               Object bo = diagramProvider.getFeatureProvider().getBusinessObjectForPictogramElement(pe);
               if (isBusinessObjectSupported(bo)) {
                  result = (T)bo;
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Checks if the given business object is supported, which
    * means that it is an instance of {@code T}.
    * @param bo The business object to check.
    * @return {@code true} is supported, {@code false} is not supported.
    */
   protected abstract boolean isBusinessObjectSupported(Object bo);

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public IDiagramEditor getDiagramEditor() {
      IDiagramEditor editor = super.getDiagramEditor();
      if (editor == null) {
         IWorkbenchPart part = getPart();
         if (part != null) {
            IEditorPart editPart = (IEditorPart)part.getAdapter(IEditorPart.class);
            if (editPart instanceof IDiagramEditor) {
               editor = (IDiagramEditor)editPart;
            }
         }
      }
      return editor;
   }
}