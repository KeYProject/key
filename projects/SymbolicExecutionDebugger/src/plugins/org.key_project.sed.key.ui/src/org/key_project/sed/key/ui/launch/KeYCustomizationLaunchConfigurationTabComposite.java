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

package org.key_project.sed.key.ui.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.key.core.launch.KeYLaunchSettings;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.ui.util.LogUtil;

/**
 * Contains the controls to define customization settings.
 * @author Martin Hentschel
 */
public class KeYCustomizationLaunchConfigurationTabComposite extends AbstractTabbedPropertiesAndLaunchConfigurationTabComposite {
   /**
    * Defines if method return values are shown or not.
    */
   private Button showMethodReturnValuesInDebugNodesButton;

   /**
    * Defines if variables of selected debug node should be shown.
    */
   private Button showVariablesOfSelectedDebugNodeButton;

   /**
    * Defines if KeY's main window is shown or not.
    */
   private Button showKeYMainWindowButton;
   
   /**
    * Defines to merge branch conditions.
    */
   private Button mergeBranchConditionsButton;
   
   /**
    * Defines to use pretty printing or not..
    */
   private Button usePrettyPrintingButton;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    * @param parentTab An optional {@link AbstractTabbedPropertiesAndLaunchConfigurationTab} to make this {@link Composite} editable.
    * @param widgetFactory An optional {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public KeYCustomizationLaunchConfigurationTabComposite(Composite parent,
                                                          int style, 
                                                          AbstractTabbedPropertiesAndLaunchConfigurationTab parentTab,
                                                          TabbedPropertySheetWidgetFactory widgetFactory) {
      super(parent, style, parentTab);
      setLayout(new FillLayout());
      if (widgetFactory == null) {
         widgetFactory = new NoFormTabbedPropertySheetWidgetFactory();
      }
      // Content composite
      Composite composite = widgetFactory.createFlatFormComposite(this);
      composite.setLayout(new GridLayout(1, false));
      // Symbolic execution tree
      Group symbolicExecutionTreeGroup = widgetFactory.createGroup(composite, "Symbolic Execution Tree");
      symbolicExecutionTreeGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      symbolicExecutionTreeGroup.setLayout(new GridLayout(1, false));
      showMethodReturnValuesInDebugNodesButton = widgetFactory.createButton(symbolicExecutionTreeGroup, "&Show method return values in debug nodes", SWT.CHECK);
      showMethodReturnValuesInDebugNodesButton.setEnabled(isEditable());
      showMethodReturnValuesInDebugNodesButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
      showVariablesOfSelectedDebugNodeButton = widgetFactory.createButton(symbolicExecutionTreeGroup, "&Show &variables of selected debug node", SWT.CHECK);
      showVariablesOfSelectedDebugNodeButton.setEnabled(isEditable());
      showVariablesOfSelectedDebugNodeButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
      mergeBranchConditionsButton = widgetFactory.createButton(symbolicExecutionTreeGroup, "&Merge branch conditions", SWT.CHECK);
      mergeBranchConditionsButton.setEnabled(isEditable());
      mergeBranchConditionsButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
      usePrettyPrintingButton = widgetFactory.createButton(symbolicExecutionTreeGroup, "Use &pretty printing", SWT.CHECK);
      usePrettyPrintingButton.setEnabled(isEditable());
      usePrettyPrintingButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
      // KeY
      Group keyGroup = widgetFactory.createGroup(composite, "KeY");
      keyGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      keyGroup.setLayout(new GridLayout(1, false));
      showKeYMainWindowButton = widgetFactory.createButton(keyGroup, "Show KeY's &main window (only for experienced user)", SWT.CHECK);
      showKeYMainWindowButton.setEnabled(isEditable());
      showKeYMainWindowButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNotValidMessage() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeFrom(ILaunchConfiguration configuration) {
      try {
         showMethodReturnValuesInDebugNodesButton.setSelection(KeySEDUtil.isShowMethodReturnValuesInDebugNodes(configuration));
         showVariablesOfSelectedDebugNodeButton.setSelection(KeySEDUtil.isShowVariablesOfSelectedDebugNode(configuration));
         showKeYMainWindowButton.setSelection(KeySEDUtil.isShowKeYMainWindow(configuration));
         mergeBranchConditionsButton.setSelection(KeySEDUtil.isMergeBranchConditions(configuration));
         usePrettyPrintingButton.setSelection(KeySEDUtil.isUsePrettyPrinting(configuration));
      } 
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeFrom(KeYLaunchSettings launchSettings) {
      showMethodReturnValuesInDebugNodesButton.setSelection(launchSettings.isShowMethodReturnValues());
      showVariablesOfSelectedDebugNodeButton.setSelection(launchSettings.isShowVariablesOfSelectedDebugNode());
      showKeYMainWindowButton.setSelection(launchSettings.isShowKeYMainWindow());
      mergeBranchConditionsButton.setSelection(launchSettings.isMergeBranchConditions());
      usePrettyPrintingButton.setSelection(launchSettings.isUsePrettyPrinting());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void performApply(ILaunchConfigurationWorkingCopy configuration) {
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, showMethodReturnValuesInDebugNodesButton.getSelection());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_VARIABLES_OF_SELECTED_DEBUG_NODE, showVariablesOfSelectedDebugNodeButton.getSelection());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_KEY_MAIN_WINDOW, showKeYMainWindowButton.getSelection());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_MERGE_BRANCH_CONDITIONS, mergeBranchConditionsButton.getSelection());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_USE_PRETTY_PRINTING, usePrettyPrintingButton.getSelection());
   }
}