package org.key_project.sed.ui.visualization.execution_tree.property;

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
import org.key_project.sed.ui.property.NodeTabComposite;

/**
 * {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public class GraphitiDebugNodePropertySection extends GFPropertySection {
   /**
    * The shown content.
    */
   private NodeTabComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = new NodeTabComposite(parent, SWT.NONE, getWidgetFactory());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      contentComposite.updateContent(getDebugNode());
   }
   
   /**
    * Returns the {@link ISEDDebugNode} to show.
    * @return The {@link ISEDDebugNode} to show or {@code null} if no one should be shown.
    */
   public ISEDDebugNode getDebugNode() {
      return getDebugNode(getSelectedPictogramElement());
   }
   
   /**
    * Returns the {@link ISEDDebugNode} to show.
    * @param pe The currently selected {@link PictogramElement}.
    * @return The {@link ISEDDebugNode} to show or {@code null} if no one should be shown.
    */
   public ISEDDebugNode getDebugNode(PictogramElement pe) {
      ISEDDebugNode node = null;
      if (pe != null) {
         IDiagramTypeProvider diagramProvider = getDiagramTypeProvider();
         if (diagramProvider != null) {
            IFeatureProvider featureProvider = diagramProvider.getFeatureProvider();
            if (featureProvider != null) {
               Object bo = diagramProvider.getFeatureProvider().getBusinessObjectForPictogramElement(pe);
               if (bo instanceof ISEDDebugNode) {
                  node = (ISEDDebugNode)bo;
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