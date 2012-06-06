package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.eclipse.graphiti.ui.platform.GFPropertySection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

/**
 * {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public class GraphitiDebugNodePropertySection extends GFPropertySection {
   /**
    * Shows the value of {@link ISEDDebugNode#getName()}.
    */
   private Text nameText;
   
   /**
    * Shows the value of {@link ISEDDebugNode#getPathCondition()}.
    */
   private Text pathText;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);

      TabbedPropertySheetWidgetFactory factory = getWidgetFactory();
      Composite composite = factory.createFlatFormComposite(parent);

      nameText = factory.createText(composite, StringUtil.EMPTY_STRING);
      nameText.setEditable(false);
      FormData data = new FormData();
      data.left = new FormAttachment(0, STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      nameText.setLayoutData(data);

      CLabel nameLabel = factory.createCLabel(composite, "Name:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nameText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nameText, 0, SWT.CENTER);
      nameLabel.setLayoutData(data);

      pathText = factory.createText(composite, StringUtil.EMPTY_STRING);
      pathText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nameText, 0, ITabbedPropertyConstants.VSPACE);
      pathText.setLayoutData(data);
      
      CLabel pathLabel = factory.createCLabel(composite, "Path:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(pathText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(pathText, 0, SWT.CENTER);
      pathLabel.setLayoutData(data);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      String name = null;
      String path = null;
      try {
         PictogramElement pe = getSelectedPictogramElement();
         if (pe != null) {
            IDiagramTypeProvider diagramProvider = getDiagramTypeProvider();
            if (diagramProvider != null) {
               IFeatureProvider featureProvider = diagramProvider.getFeatureProvider();
               if (featureProvider != null) {
                  Object bo = diagramProvider.getFeatureProvider().getBusinessObjectForPictogramElement(pe);
                  if (bo instanceof ISEDDebugNode) {
                     name = ((ISEDDebugNode)bo).getName();
                     path = ((ISEDDebugNode)bo).getPathCondition();
                  }
               }
            }
         }
         SWTUtil.setText(nameText, name);
         SWTUtil.setText(pathText, path);
      }
      catch (DebugException e) {
         name = e.getMessage();
         LogUtil.getLogger().logError(e);
         SWTUtil.setText(nameText, name);
         SWTUtil.setText(pathText, name);
      }
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

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public Diagram getDiagram() {
      return super.getDiagram();
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
   public IDiagramTypeProvider getDiagramTypeProvider() {
      return super.getDiagramTypeProvider();
   }
}