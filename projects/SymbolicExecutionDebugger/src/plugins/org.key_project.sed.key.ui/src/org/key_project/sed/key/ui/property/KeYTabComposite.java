package org.key_project.sed.key.ui.property;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.proof.Node;

/**
 * This composite provides the content shown in {@link KeYDebugNodePropertySection}
 * and {@link KeYGraphitiDebugNodePropertySection}.
 * @author Martin Hentschel
 */
public class KeYTabComposite extends Composite {
   /**
    * Shows the node id with applied rule of the node in KeY's proof tree represented by the current {@link IKeYSEDDebugNode}.
    */
   private Text nodeText;
   
   /**
    * Shows the sequent of the node in KeY's proof tree represented by the current {@link IKeYSEDDebugNode}.
    */
   private Text sequentText;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public KeYTabComposite(Composite parent, int style, TabbedPropertySheetWidgetFactory factory) {
      super(parent, style);
      setLayout(new FillLayout());
      
      Composite composite = factory.createFlatFormComposite(this);

      nodeText = factory.createText(composite, StringUtil.EMPTY_STRING);
      nodeText.setEditable(false);
      FormData data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      nodeText.setLayoutData(data);

      CLabel nodeLabel = factory.createCLabel(composite, "Node:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nodeText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nodeText, 0, SWT.CENTER);
      nodeLabel.setLayoutData(data);

      sequentText = factory.createText(composite, StringUtil.EMPTY_STRING, SWT.MULTI);
      sequentText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nodeText, 0, ITabbedPropertyConstants.VSPACE);
      sequentText.setLayoutData(data);
      
      CLabel sequentLabel = factory.createCLabel(composite, "Sequent:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(sequentText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(sequentText, 0, SWT.TOP);
      sequentLabel.setLayoutData(data);
   }
   
   /**
    * Updates the shown content.
    * @param node The {@link IKeYSEDDebugNode} which provides the new content.
    */
   public void updateContent(IKeYSEDDebugNode<?> node) {
      String name = null;
      String sequent = null;
      if (node != null) {
         Node keyNode = node.getExecutionNode().getProofNode();
         name = keyNode.serialNr() + ": " + keyNode.name(); // Copied from ProofRenderer
         sequent = NonGoalInfoView.computeText(node.getExecutionNode().getMediator(), 
                                               keyNode);
      }
      SWTUtil.setText(nodeText, name);
      SWTUtil.setText(sequentText, sequent);
   }
}
