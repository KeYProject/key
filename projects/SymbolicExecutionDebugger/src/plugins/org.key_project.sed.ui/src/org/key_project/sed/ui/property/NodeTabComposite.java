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

package org.key_project.sed.ui.property;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.util.java.StringUtil;

/**
 * This composite provides the content shown in {@link SEDDebugNodePropertySection}
 * and in {@code GraphitiDebugNodePropertySection}.
 * @author Martin Hentschel
 */
public class NodeTabComposite implements ISEDDebugNodeTabContent {
   /**
    * The parent {@link Composite};
    */
   private Composite parent;
   
   /**
    * The currently shown {@link Composite}.
    */
   private Composite composite;

   /**
    * The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   private TabbedPropertySheetWidgetFactory factory;
   
   /**
    * Constructor.
    */
   public NodeTabComposite() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createComposite(Composite parent, TabbedPropertySheetWidgetFactory factory) {
      this.factory = factory;
      this.parent = parent;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(ISEDDebugNode node) {
      String name = null;
      String type = null;
      String path = null;
      String returnCondition = null;
      try {
         if (node != null) {
            name = node.getName();
            type = node.getNodeType();
            if (!node.getDebugTarget().isTerminated()) {
               path = node.getPathCondition();
            }
            if (node instanceof ISEDMethodReturn) {
               ISEDBranchCondition returnBranchCondition = ((ISEDMethodReturn) node).getMethodReturnCondition();
               if (returnBranchCondition != null) {
                  returnCondition = returnBranchCondition.getName();
               }
            }
         }
      }
      catch (DebugException e) {
         name = e.getMessage();
         LogUtil.getLogger().logError(e);
      }
      recreateContent(name, type, SEDImages.getNodeImage(node), path, returnCondition);
   }
   
   /**
    * Updates the shown content by recreating it.
    */
   protected void recreateContent(String name,
                                  String type,
                                  Image typeImage,
                                  String path,
                                  String returnCondition) {
      disposeContent();
      createContent(name, type, typeImage, path, returnCondition);
      parent.layout();
      parent.getParent().layout();
   }
   
   /**
    * Disposes the currently shown content.
    */
   protected void disposeContent() {
      if (composite != null) {
         composite.setVisible(false);
         composite.dispose();
         composite = null;
      }
   }

   /**
    * Creates a new content which shows the given values.
    */
   protected void createContent(String name,
                                String type,
                                Image typeImage,
                                String path,
                                String returnCondition) {
      int labelWidth = returnCondition != null ? 115 : AbstractPropertySection.STANDARD_LABEL_WIDTH;

      composite = factory.createFlatFormComposite(parent);

      Text nameText = factory.createText(composite, name != null ? name : StringUtil.EMPTY_STRING);
      nameText.setEditable(false);
      FormData data = new FormData();
      data.left = new FormAttachment(0, labelWidth);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      nameText.setLayoutData(data);

      CLabel nameLabel = factory.createCLabel(composite, "Name:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nameText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nameText, 0, SWT.CENTER);
      nameLabel.setLayoutData(data);

      CLabel typeCLabel = factory.createCLabel(composite, type);
      typeCLabel.setImage(typeImage);
      data = new FormData();
      data.left = new FormAttachment(0, labelWidth);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nameText, 0, ITabbedPropertyConstants.VSPACE);
      typeCLabel.setLayoutData(data);

      CLabel typeLabel = factory.createCLabel(composite, "Type:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(typeCLabel, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(typeCLabel, 0, SWT.CENTER);
      typeLabel.setLayoutData(data);

      Text pathText = factory.createText(composite, path != null ? path : StringUtil.EMPTY_STRING);
      pathText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, labelWidth);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(typeCLabel, 0, ITabbedPropertyConstants.VSPACE);
      pathText.setLayoutData(data);
      
      CLabel pathLabel = factory.createCLabel(composite, "Path:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(pathText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(pathText, 0, SWT.CENTER);
      pathLabel.setLayoutData(data);

      if (returnCondition != null) {
         Text methodReturnText = factory.createText(composite, returnCondition);
         methodReturnText.setEditable(false);
         data = new FormData();
         data.left = new FormAttachment(0, labelWidth);
         data.right = new FormAttachment(100, 0);
         data.top = new FormAttachment(pathLabel, 0, ITabbedPropertyConstants.VSPACE);
         methodReturnText.setLayoutData(data);
         
         CLabel methodReturnLabel = factory.createCLabel(composite, "Return Condition:");
         data = new FormData();
         data.left = new FormAttachment(0, 0);
         data.right = new FormAttachment(methodReturnText, -ITabbedPropertyConstants.HSPACE);
         data.top = new FormAttachment(methodReturnText, 0, SWT.CENTER);
         methodReturnLabel.setLayoutData(data);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
   }
}