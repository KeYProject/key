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
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

/**
 * {@link ISection} implementation to show properties of {@link ODAssociation}s.
 * @author Martin Hentschel
 */
public class AssociationPropertySection extends AbstractObjectDiagramPropertySection<ODAssociation> {
   /**
    * Shows {@link ODAssociation#getName()}.
    */
   private Text nameText;

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
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      ODAssociation object = getBusinessObject();
      if (object != null) {
         SWTUtil.setText(nameText, object.getName());
      }
      else {
         nameText.setText(StringUtil.EMPTY_STRING);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isBusinessObjectSupported(Object bo) {
      return bo instanceof ODAssociation;
   }
}