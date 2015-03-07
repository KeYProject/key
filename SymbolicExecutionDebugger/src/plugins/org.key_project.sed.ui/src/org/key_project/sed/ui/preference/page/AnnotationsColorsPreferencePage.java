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

package org.key_project.sed.ui.preference.page;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.sed.core.util.SEDPreferenceUtil;

/**
 * Preference page for the colors of {@link ISEDAnnotationType}s.
 * @author Martin Hentschel
 */
public class AnnotationsColorsPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public AnnotationsColorsPreferencePage() {
      super(GRID);
      setPreferenceStore(SEDPreferenceUtil.getStore());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void createFieldEditors() {
      GridLayout parentlLayout = (GridLayout)getFieldEditorParent().getLayout();
      for (ISEDAnnotationType type : SEDAnnotationUtil.getAnnotationtypes()) {
         final Group group = new Group(getFieldEditorParent(), SWT.NONE);
         GridData groupLayoutData = new GridData(GridData.FILL_HORIZONTAL);
         groupLayoutData.horizontalSpan = parentlLayout.numColumns + 1;
         group.setLayoutData(groupLayoutData);
         group.setText(type.getName());
         group.setLayout(new GridLayout(5, false));
         
         final ColorBooleanFieldEditor highlightBackgroundEditor = new ColorBooleanFieldEditor(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX + type.getTypeId(), "Highlight Background Color", group);
         addField(highlightBackgroundEditor);
         final ColorFieldEditor backgroundEditor = new ColorFieldEditor(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX + type.getTypeId(), "Background Color", group);
         addField(backgroundEditor);
         final ColorBooleanFieldEditor highlightForegroundEditor = new ColorBooleanFieldEditor(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX + type.getTypeId(), "Highlight Foreground Color", group);
         addField(highlightForegroundEditor);
         final ColorFieldEditor foregroundEditor = new ColorFieldEditor(SEDPreferenceUtil.PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX + type.getTypeId(), "Foreground Color", group);
         addField(foregroundEditor);
         
         highlightBackgroundEditor.setColorEditor(backgroundEditor);
         highlightForegroundEditor.setColorEditor(foregroundEditor);
      }
   }
   
   /**
    * An extended {@link BooleanFieldEditor} which updates the enabled state
    * of the defined {@link ColorFieldEditor}.
    * @author Martin Hentschel
    */
   private static class ColorBooleanFieldEditor extends BooleanFieldEditor {
      /**
       * The parent {@link Composite}.
       */
      private final Composite parent;
      
      /**
       * The {@link ColorFieldEditor}.
       */
      private ColorFieldEditor colorEditor;
      
      /**
       * Constructor.
       * @param name Name.
       * @param label Label.
       * @param parent Parent {@link Composite}.
       */
      public ColorBooleanFieldEditor(String name, String label, Composite parent) {
         super(name, label, parent);
         this.parent = parent;
      }

      /**
       * Sets the {@link ColorFieldEditor}.
       * @param colorEditor The {@link ColorFieldEditor}.
       */
      public void setColorEditor(ColorFieldEditor colorEditor) {
         this.colorEditor = colorEditor;
         updateColorEditorEnabled();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void doLoad() {
         super.doLoad();
         updateColorEditorEnabled();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void doLoadDefault() {
         super.doLoadDefault();
         updateColorEditorEnabled();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      protected void valueChanged(boolean oldValue, boolean newValue) {
         super.valueChanged(oldValue, newValue);
         updateColorEditorEnabled();
      }      
      
      /**
       * Updates the enabled state of the {@link ColorFieldEditor}.
       */
      protected void updateColorEditorEnabled() {
         if (colorEditor != null) {
            colorEditor.setEnabled(getBooleanValue(), parent);
         }
      }
   }
}