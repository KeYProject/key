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

package org.key_project.sed.ui.property;

import org.eclipse.debug.core.DebugException;
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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

/**
 * This composite provides the content shown in {@link SEDDebugNodePropertySection}
 * and in {@code GraphitiDebugNodePropertySection}.
 * @author Martin Hentschel
 */
public class NodeTabComposite extends AbstractSEDDebugNodeTabComposite {
   /**
    * Shows the value of {@link ISEDDebugNode#getName()}.
    */
   private Text nameText;
   
   /**
    * Shows the value of {@link ISEDDebugNode#getNodeType()}.
    */
   private CLabel typeCLabel;
   
   /**
    * Shows the value of {@link ISEDDebugNode#getPathCondition()}.
    */
   private Text pathText;

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public NodeTabComposite(Composite parent, int style, TabbedPropertySheetWidgetFactory factory) {
      super(parent, style);
      setLayout(new FillLayout());
      
      Composite composite = factory.createFlatFormComposite(this);

      nameText = factory.createText(composite, StringUtil.EMPTY_STRING);
      nameText.setEditable(false);
      FormData data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      nameText.setLayoutData(data);

      CLabel nameLabel = factory.createCLabel(composite, "Name:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nameText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nameText, 0, SWT.CENTER);
      nameLabel.setLayoutData(data);

      typeCLabel = factory.createCLabel(composite, StringUtil.EMPTY_STRING);
      data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nameText, 0, ITabbedPropertyConstants.VSPACE);
      typeCLabel.setLayoutData(data);

      CLabel typeLabel = factory.createCLabel(composite, "Type:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(typeCLabel, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(typeCLabel, 0, SWT.CENTER);
      typeLabel.setLayoutData(data);

      pathText = factory.createText(composite, StringUtil.EMPTY_STRING);
      pathText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(typeCLabel, 0, ITabbedPropertyConstants.VSPACE);
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
   public void updateContent(ISEDDebugNode node) {
      String name = null;
      String type = null;
      String path = null;
      try {
         if (node != null) {
            name = node.getName();
            type = node.getNodeType();
            if (!node.getDebugTarget().isTerminated()) {
               path = node.getPathCondition();
            }
         }
      }
      catch (DebugException e) {
         name = e.getMessage();
         LogUtil.getLogger().logError(e);
      }
      SWTUtil.setText(nameText, name);
      typeCLabel.setText(type);
      typeCLabel.setImage(SEDImages.getNodeImage(node));
      SWTUtil.setText(pathText, path);
   }
}