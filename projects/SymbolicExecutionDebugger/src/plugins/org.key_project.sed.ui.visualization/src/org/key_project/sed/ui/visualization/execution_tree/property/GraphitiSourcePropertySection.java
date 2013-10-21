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

package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.eclipse.graphiti.ui.platform.GFPropertySection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.property.SourceTabComposite;

/**
 * {@link ISection} implementation to show source of {@link IStackFrame}s.
 * @author Martin Hentschel
 */
public class GraphitiSourcePropertySection extends GFPropertySection {
   /**
    * The shown content.
    */
   private SourceTabComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = new SourceTabComposite(parent, SWT.NONE, getWidgetFactory());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      contentComposite.updateContent(getStackFrame());
   }
   
   /**
    * Returns the {@link IStackFrame} to show.
    * @return The {@link IStackFrame} to show or {@code null} if no one should be shown.
    */
   public IStackFrame getStackFrame() {
      return getStackFrame(getSelectedPictogramElement());
   }
   
   /**
    * Returns the {@link IStackFrame} to show.
    * @param pe The currently selected {@link PictogramElement}.
    * @return The {@link IStackFrame} to show or {@code null} if no one should be shown.
    */
   public IStackFrame getStackFrame(PictogramElement pe) {
      IStackFrame node = null;
      if (pe != null) {
         IDiagramTypeProvider diagramProvider = getDiagramTypeProvider();
         if (diagramProvider != null) {
            IFeatureProvider featureProvider = diagramProvider.getFeatureProvider();
            if (featureProvider != null) {
               Object bo = diagramProvider.getFeatureProvider().getBusinessObjectForPictogramElement(pe);
               if (bo instanceof ISEDDebugNode && bo instanceof IStackFrame) {
                  IStackFrame frame = (IStackFrame)bo;
                  if (frame.getLaunch() != null) {
                     node = frame;
                  }
               }
            }
         }
      }
      return node;
   }

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