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
public class SEDDebugNodePropertySection extends GFPropertySection {
   /**
    * Shows the value of {@link ISEDDebugNode#getName()}.
    */
   private Text nameText;

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

      CLabel valueLabel = factory.createCLabel(composite, "Name:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nameText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nameText, 0, SWT.CENTER);
      valueLabel.setLayoutData(data);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      String name = null;
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
                  }
               }
            }
         }
         SWTUtil.setText(nameText, name);
      }
      catch (DebugException e) {
         name = e.getMessage();
         LogUtil.getLogger().logError(e);
      }
      SWTUtil.setText(nameText, name);
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
      return super.getDiagramEditor();
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