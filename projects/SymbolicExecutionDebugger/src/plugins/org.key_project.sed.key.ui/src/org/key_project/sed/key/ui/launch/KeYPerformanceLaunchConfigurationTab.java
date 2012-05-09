package org.key_project.sed.key.ui.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.ui.util.KeYSEDImages;
import org.key_project.sed.key.ui.util.LogUtil;

/**
 * {@link AbstractLaunchConfigurationTab} implementation for the
 * performance options of the Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYPerformanceLaunchConfigurationTab extends AbstractLaunchConfigurationTab {
   /**
    * Defines if method return values are shown or not.
    */
   private Button showMethodReturnValuesInDebugNodesButton;
  
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Performance";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return KeYSEDImages.getImage(KeYSEDImages.LAUNCH_PERFORMANCE_TAB_GROUP);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Root
      Composite rootComposite = new Composite(parent, SWT.NONE);
      setControl(rootComposite);
      rootComposite.setLayout(new GridLayout(1, false));
      // Symbolic execution tree
      Group symbolicExecutionTreeGroup = new Group(rootComposite, SWT.NONE);
      symbolicExecutionTreeGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      symbolicExecutionTreeGroup.setText("Symbolic Execution Tree");
      symbolicExecutionTreeGroup.setLayout(new GridLayout(1, false));
      showMethodReturnValuesInDebugNodesButton = new Button(symbolicExecutionTreeGroup, SWT.CHECK);
      showMethodReturnValuesInDebugNodesButton.setText("&Show method return values in debug nodes");
      showMethodReturnValuesInDebugNodesButton.addSelectionListener(new SelectionAdapter() {
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
   public void setDefaults(ILaunchConfigurationWorkingCopy configuration) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeFrom(ILaunchConfiguration configuration) {
      try {
         showMethodReturnValuesInDebugNodesButton.setSelection(KeySEDUtil.isShowMethodReturnValuesInDebugNodes(configuration));
      } 
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void performApply(ILaunchConfigurationWorkingCopy configuration) {
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, showMethodReturnValuesInDebugNodesButton.getSelection());
   }
}
