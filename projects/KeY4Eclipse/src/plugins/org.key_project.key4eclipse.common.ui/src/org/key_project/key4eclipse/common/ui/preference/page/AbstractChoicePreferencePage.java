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

package org.key_project.key4eclipse.common.ui.preference.page;

import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.preference.IPreferencePage;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.ButtonViewer;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.ChoiceSettings;

/**
 * Provides a basic {@link IPreferencePage} implementation to edit
 * {@link ChoiceSettings}.
 * @author Martin Hentschel
 */
public abstract class AbstractChoicePreferencePage extends PreferencePage implements IWorkbenchPreferencePage {
   /**
    * The {@link ChoiceSettings} to edit.
    */
   private ChoiceSettings choiceSettings;
   
   /**
    * Reference to {@link ChoiceSettings#getDefaultChoices()} of {@link #choiceSettings}.
    */
   private HashMap<String, String> category2DefaultChoice;
   
   /**
    * Reference to {@link ChoiceSettings#getChoices()} of {@link #choiceSettings}.
    */
   private HashMap<String, Set<String>> category2Choices;
   
   /**
    * Maps the category to the {@link ButtonViewer} which allows the user to change the setting.
    */
   private Map<String, ButtonViewer> category2ChoiceViewerMapping = new HashMap<String, ButtonViewer>();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
      if (isChoiceSettingsLoadingRequired()) {
         doLoadChoiceSettings();
      }
      choiceSettings = getChoiceSettings();
      category2DefaultChoice = choiceSettings.getDefaultChoices();
      category2Choices = choiceSettings.getChoices();
   }
   
   /**
    * Checks if it is required to load the {@link ChoiceSettings} or
    * if they are already available.
    * @return {@code true} load {@link ChoiceSettings}, {@code false} {@link ChoiceSettings} already available.
    */
   protected abstract boolean isChoiceSettingsLoadingRequired();

   /**
    * Loads the {@link ChoiceSettings} if required in a different {@link Thread}
    * and shows the progress to the user in a dialog.
    */
   protected void doLoadChoiceSettings() {
      try {
         PlatformUI.getWorkbench().getProgressService().run(true, false, new IRunnableWithProgress() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               loadChoiceSettings(monitor);
            }
         });
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getControl() != null ? getShell() : null, e);
      }
   }
   
   /**
    * Loads the {@link ChoiceSettings}.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws InvocationTargetException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   protected abstract void loadChoiceSettings(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException;
   
   /**
    * Returns the {@link ChoiceSettings} to edit.
    * @return The {@link ChoiceSettings} to edit.
    */
   protected abstract ChoiceSettings getChoiceSettings();

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(Composite parent) {
      // Create root composite
      Composite rootComposite = new Composite(parent, SWT.NONE);
      rootComposite.setLayout(new GridLayout(1, false));
      // Create categories viewer
      TabFolder categoriesTabFolder = new TabFolder(rootComposite, SWT.NONE);
      categoriesTabFolder.setLayoutData(new GridData(GridData.FILL_BOTH));
      String[] categories = computeCategories(category2DefaultChoice);
      for (String category : categories) {
         TabItem categoryTabItem = new TabItem(categoriesTabFolder, SWT.NONE);
         categoryTabItem.setText(category);
         Composite tabComposite = new Composite(categoriesTabFolder, SWT.NONE);
         tabComposite.setLayout(new GridLayout(1, false));
         categoryTabItem.setControl(tabComposite);
         
         Group settingsGroup = new Group(tabComposite, SWT.NONE);
         settingsGroup.setText("Settings");
         settingsGroup.setLayout(new FillLayout());
         settingsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         ButtonViewer settingsViewer = new ButtonViewer(settingsGroup, SWT.RADIO);
         settingsViewer.setContentProvider(ArrayContentProvider.getInstance());
         settingsViewer.setInput(category2Choices.get(category));
         settingsViewer.setSelection(SWTUtil.createSelection(category2DefaultChoice.get(category)));
         category2ChoiceViewerMapping.put(category, settingsViewer);
         
         Group explanationGroup = new Group(tabComposite, SWT.NONE);
         explanationGroup.setText("Explanation");
         explanationGroup.setLayout(new FillLayout());
         explanationGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
         Text explanationText = new Text(explanationGroup, SWT.BORDER | SWT.MULTI | SWT.V_SCROLL | SWT.WRAP);
         explanationText.setEditable(false);
         String explanation = ChoiceSelector.getExplanation(category);
         SWTUtil.setText(explanationText, StringUtil.trim(explanation));
      }
      return rootComposite;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Point doComputeSize() {
      return new Point(0, 0);
   }

   /**
    * Computes the categories to show.
    * @param category2DefaultChoice The category to setting mapping.
    * @return The categories to show.
    */
   protected String[] computeCategories(HashMap<String, String> category2DefaultChoice) {
      Set<String> keys = category2DefaultChoice.keySet();
      String[] cats = keys.toArray(new String[keys.size()]);
      Arrays.sort(cats);
      return cats;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performDefaults() {
      Map<String, String> defaults = getDefaults();
      if (defaults != null) {
         for (Entry<String, String> entry : defaults.entrySet()) {
            ButtonViewer viewer = category2ChoiceViewerMapping.get(entry.getKey());
            viewer.setSelection(SWTUtil.createSelection(entry.getValue()));
         }
      }
   }
   
   /**
    * Returns the default values.
    * @return The default values.
    */
   public abstract Map<String, String> getDefaults();

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performApply() {
      applyChanges();
      super.performApply();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performOk() {
      applyChanges();
      return super.performOk();
   }
   
   /**
    * Applies the values defined by the user in the UI to the edited {@link ChoiceSettings}.
    */
   protected void applyChanges() {
      Set<Entry<String, ButtonViewer>> entries = category2ChoiceViewerMapping.entrySet();
      for (Entry<String, ButtonViewer> entry : entries) {
         ISelection selection = entry.getValue().getSelection();
         Object selectedElement = SWTUtil.getFirstElement(selection);
         Assert.isTrue(selectedElement instanceof String);
         category2DefaultChoice.put(entry.getKey(), (String)selectedElement);
      }
      choiceSettings.setDefaultChoices(category2DefaultChoice);
   }
}