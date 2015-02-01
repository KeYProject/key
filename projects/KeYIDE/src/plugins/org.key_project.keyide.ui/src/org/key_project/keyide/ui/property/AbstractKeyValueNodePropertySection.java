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

package org.key_project.keyide.ui.property;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

/**
 * Provides the basic functionality to show multiple key value pairs.
 * @author Martin Hentschel
 */
public abstract class AbstractKeyValueNodePropertySection extends AbstractNodePropertySection {
   /**
    * The parent {@link Composite}.
    */
   private Composite parent;
   
   /**
    * The {@link TabbedPropertySheetPage} to use.
    */
   private TabbedPropertySheetPage tabbedPropertySheetPage;
   
   /**
    * Maps keys to the {@link Text} control which shows the value.
    */
   private Map<String, Text> controlMapping = new HashMap<String, Text>();
   
   /**
    * The last added {@link Text}.
    */
   private Text previous;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      this.tabbedPropertySheetPage = tabbedPropertySheetPage;
      super.createControls(parent, tabbedPropertySheetPage);
      TabbedPropertySheetWidgetFactory factory = getWidgetFactory();
      this.parent = factory.createFlatFormComposite(parent);
   }
   
   /**
    * Resets all texts.
    */
   protected void resetTexts() {
      for (Text text : controlMapping.values()) {
         text.setText(StringUtil.EMPTY_STRING);
      }
   }
   
   /**
    * Shows the given key value pair.
    * @param key The key.
    * @param value The value to show.
    * @param tooltip An optional tool tip text to show.
    */
   protected void showText(String key, String value, String tooltip) {
      Text text = controlMapping.get(key);
      if (text == null) {
         text = tabbedPropertySheetPage.getWidgetFactory().createText(parent, value != null ? value : StringUtil.EMPTY_STRING);
         if (tooltip != null) {
            text.setToolTipText(tooltip);
         }
         addControlRow(tabbedPropertySheetPage.getWidgetFactory(), parent, previous, text, key);
         previous = text;
         controlMapping.put(key, text);
      }
      else {
         SWTUtil.setText(text, value);
      }
   }
}