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

package org.key_project.sed.key.ui.property;

import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.eclipse.graphiti.ui.platform.GFPropertySection;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;

/**
 * Basic {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s
 * in a {@link AbstractPredicateComposite}.
 * @author Martin Hentschel
 */
public abstract class AbstractPredicateGraphitiPropertySection extends GFPropertySection {
   /**
    * The shown content.
    */
   private AbstractPredicateComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = createContentComposite(parent);
   }
   
   /**
    * Creates the {@link AbstractPredicateComposite} to show.
    * @param parent The parent {@link Composite}.
    * @return The created {@link AbstractPredicateComposite}.
    */
   protected abstract AbstractPredicateComposite createContentComposite(Composite parent);

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (contentComposite != null) {
         contentComposite.dispose();
      }
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      contentComposite.updateContent(getDebugNode());
   }
   
   /**
    * Returns the {@link IKeYSEDDebugNode} to show.
    * @return The {@link IKeYSEDDebugNode} to show or {@code null} if no one should be shown.
    */
   public IKeYSEDDebugNode<?> getDebugNode() {
      return getDebugNode(getSelectedPictogramElement());
   }
   
   /**
    * Returns the {@link IKeYSEDDebugNode} to show.
    * @param pe The currently selected {@link PictogramElement}.
    * @return The {@link IKeYSEDDebugNode} to show or {@code null} if no one should be shown.
    */
   public abstract IKeYSEDDebugNode<?> getDebugNode(PictogramElement pe);

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