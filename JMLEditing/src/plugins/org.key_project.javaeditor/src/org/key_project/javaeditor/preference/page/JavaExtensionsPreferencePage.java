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

package org.key_project.javaeditor.preference.page;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ICheckStateProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Table;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.javaeditor.util.ExtendableConfigurationUtil;
import org.key_project.javaeditor.util.ExtendableConfigurationUtil.ExtensionDescription;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.key_project.util.eclipse.preference.ObservableBooleanFieldEditor;
import org.key_project.util.eclipse.preference.event.FieldEditorValueEvent;
import org.key_project.util.eclipse.preference.event.IFieldEditorValueListener;
import org.key_project.util.java.ObjectUtil;

/**
 * Preference page for the Java extensions.
 * @author Martin Hentschel
 */
public class JavaExtensionsPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * The available {@link ExtensionDescription}s.
    */
   private final ExtensionDescription[] extensionDescriptions;

   /**
    * THe {@link CheckboxTableViewer} which shows {@link #extensionDescriptions}.
    */
   private CheckboxTableViewer extensionsViewer;

   /**
    * Constructor
    */
   public JavaExtensionsPreferencePage() {
      super(GRID);
      setPreferenceStore(PreferenceUtil.getStore());
      extensionDescriptions = ExtendableConfigurationUtil.getExtensionDescriptions();
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
      final ObservableBooleanFieldEditor enabledEditor = new ObservableBooleanFieldEditor(PreferenceUtil.PROP_EXTENSIONS_ENABLED, "Extensions &Enabled", getFieldEditorParent());
      addField(enabledEditor);
      Group extensionsGroup = new Group(getFieldEditorParent(), SWT.NONE);
      extensionsGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      extensionsGroup.setText("Available Extensions");
      extensionsGroup.setLayout(new GridLayout(1, false));
      extensionsViewer = new CheckboxTableViewer(new Table(extensionsGroup, SWT.BORDER | SWT.SINGLE | SWT.CHECK));
      extensionsViewer.getControl().setLayoutData(new GridData(GridData.FILL_BOTH));
      extensionsViewer.setContentProvider(ArrayContentProvider.getInstance());
      extensionsViewer.setLabelProvider(new LabelProvider() {
         @Override
         public String getText(Object element) {
            if (element instanceof ExtensionDescription) {
               return ((ExtensionDescription) element).getName();
            }
            else {
               return ObjectUtil.toString(element);
            }
         }
      });
      extensionsViewer.setCheckStateProvider(new ICheckStateProvider() {
         @Override
         public boolean isGrayed(Object element) {
            return false;
         }
         
         @Override
         public boolean isChecked(Object element) {
            if (element instanceof ExtensionDescription) {
               return PreferenceUtil.isExtensionEnabled(((ExtensionDescription) element).getId());
            }
            else {
               return false;
            }
         }
      });
      extensionsViewer.setInput(extensionDescriptions);
      enabledEditor.addFieldEditorValueListener(new IFieldEditorValueListener() {
         @Override
         public void shownValueChanged(FieldEditorValueEvent e) {
            extensionsViewer.getControl().setEnabled(enabledEditor.getBooleanValue());
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performDefaults() {
      super.performDefaults();
      for (ExtensionDescription description : extensionDescriptions) {
         extensionsViewer.setChecked(description, PreferenceUtil.isDefaultExtensionEnabled(description.getId()));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performOk() {
      boolean done = super.performOk();
      for (ExtensionDescription description : extensionDescriptions) {
         PreferenceUtil.setExtensionEnabled(description.getId(), extensionsViewer.getChecked(description));
      }
      return done;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performApply() {
      super.performApply();
      for (ExtensionDescription description : extensionDescriptions) {
         PreferenceUtil.setExtensionEnabled(description.getId(), extensionsViewer.getChecked(description));
      }
   }
}