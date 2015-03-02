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

package org.key_project.sed.ui.visualization.object_diagram.property;

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
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

/**
 * {@link ISection} implementation to show properties of {@link ODValue}s.
 * @author Martin Hentschel
 */
public class ValuePropertySection extends AbstractObjectDiagramPropertySection<ODValue> {
   /**
    * Shows {@link ODValue#getName()}.
    */
   private Text nameText;

   /**
    * Shows {@link ODValue#getValue()}.
    */
   private Text valueText;

   /**
    * Shows {@link ODValue#getType()}.
    */
   private Text typeText;

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      TabbedPropertySheetWidgetFactory factory = tabbedPropertySheetPage.getWidgetFactory();
      
      Composite composite = factory.createFlatFormComposite(parent);

      nameText = factory.createText(composite, StringUtil.EMPTY_STRING, SWT.MULTI);
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
      data.top = new FormAttachment(nameText, 0, SWT.TOP);
      nameLabel.setLayoutData(data);

      valueText = factory.createText(composite, StringUtil.EMPTY_STRING, SWT.MULTI);
      valueText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nameText, ITabbedPropertyConstants.VSPACE);
      valueText.setLayoutData(data);

      CLabel valueLabel = factory.createCLabel(composite, "Value:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(valueText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(valueText, 0, SWT.CENTER);
      valueLabel.setLayoutData(data);

      typeText = factory.createText(composite, StringUtil.EMPTY_STRING);
      typeText.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(valueText, ITabbedPropertyConstants.VSPACE);
      typeText.setLayoutData(data);

      CLabel typeLabel = factory.createCLabel(composite, "Type:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(typeText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(typeText, 0, SWT.TOP);
      typeLabel.setLayoutData(data);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      ODValue object = getBusinessObject();
      if (object != null) {
         SWTUtil.setText(nameText, object.getName());
         SWTUtil.setText(valueText, object.getValue());
         SWTUtil.setText(typeText, object.getType());
      }
      else {
         nameText.setText(StringUtil.EMPTY_STRING);
         valueText.setText(StringUtil.EMPTY_STRING);
         typeText.setText(StringUtil.EMPTY_STRING);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isBusinessObjectSupported(Object bo) {
      return bo instanceof ODValue;
   }
}