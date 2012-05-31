package org.key_project.sed.ui.property;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

/**
 * {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public class SEDDebugNodePropertySection extends AbstractPropertySection {
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
         ISEDDebugNode node = getDebugNode();
         if (node != null) {
            name = node.getName();
            path = node.getPathCondition();
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
    * Returns the {@link ISEDDebugNode} to show.
    * @return The {@link ISEDDebugNode} to show or {@code null} if no one should be shown.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDDebugNode getDebugNode() throws DebugException {
      Object object = SWTUtil.getFirstElement(getSelection());
      return object instanceof ISEDDebugNode ? (ISEDDebugNode)object : null;
   }
}