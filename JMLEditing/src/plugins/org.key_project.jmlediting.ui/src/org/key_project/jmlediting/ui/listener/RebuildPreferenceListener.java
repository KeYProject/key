package org.key_project.jmlediting.ui.listener;

import org.eclipse.swt.widgets.Shell;
import org.key_project.javaeditor.util.IPreferenceListener;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.preferencepages.RebuildHelper;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * {@link IPreferenceListener} which triggers a re-build if required.
 * @author Martin Hentschel
 */
public class RebuildPreferenceListener implements IPreferenceListener {
   /**
    * {@inheritDoc}
    */
   @Override
   public void extensionsEnabledStateChanged(boolean newEnabled) {
      // Rebuild if now enabled
      if (newEnabled && PreferenceUtil.isExtensionEnabled(JMLPreferencesHelper.JML_EDITOR_EXTENSION_ID)) {
         rebuild();
      }
      // Rebuild if now disabled
      if (!newEnabled && PreferenceUtil.isExtensionEnabled(JMLPreferencesHelper.JML_EDITOR_EXTENSION_ID)) {
         rebuild();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void extensionEnabledStateChanged(String id, boolean newEnabled) {
      if (JMLPreferencesHelper.JML_EDITOR_EXTENSION_ID.equals(id)) {
         // Rebuild if now enabled
         if (newEnabled && PreferenceUtil.isExtensionsEnabled()) {
            rebuild();
         }
         // Rebuild if now disabled
         if (!newEnabled && PreferenceUtil.isExtensionsEnabled()) {
            rebuild();
         }
      }
   }
   
   /**
    * Performs the rebuild.
    */
   protected void rebuild() {
      final Shell shell = WorkbenchUtil.getActiveShell();
      shell.getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            RebuildHelper.triggerRebuild(null, 
                                         shell,
                                         RebuildHelper.UserMessage.JML_EDITING_ON_OR_OFF, 
                                         new Runnable() {
                                            @Override
                                            public void run() {
                                            }
                                         });
         }
      });
   }
}
