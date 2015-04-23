package org.key_project.jmlediting.ui.preferencepages;

import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.util.jdt.JDTUtil;

/**
 * Helper class to trigger rebuilds on projects.
 *
 * @author Moritz Lichter
 *
 */
public final class RebuildHelper {

   /**
    * No instances.
    */
   private RebuildHelper() {
   }

   public static enum UserMessage {

      JML_EDITING_ON_OR_OFF {
         @Override
         public String getTitle() {
            return "JML Editing Turned On or Off";
         }

         @Override
         public String getMessage() {
            return "The JML Editing Plugin has been turned off or on. A full rebuild is required for changes to take effect. Do the full rebuild now?";
         }
      },
      ACTIVE_PROFILE_CHANGED {
         @Override
         public String getTitle() {
            return "Active JML Profile Changed";
         }

         @Override
         public String getMessage() {
            return "The active JML Profile has changed. A full rebuild of the affected projects is required for changes to take effect. Do the full rebuild now?";
         }
      },
      PROFILE_EDITED {
         @Override
         public String getTitle() {
            return "Profile edited";
         }

         @Override
         public String getMessage() {
            return "The derived JML Profile has changed. A full rebuild of the affected projects is required for changes to take effect. Do the full rebuild now?";
         }
      };

      public abstract String getTitle();

      public abstract String getMessage();
   }

   /**
    * Triggers a rebuild for the given projects. If the set of projects is null,
    * a rebuild for the complete workspace is triggered. This shows a dialog to
    * the user, whether he wants to do the rebuild now, later or not apply the
    * changes. Changes are applied by executing the run method of the given
    * {@link Runnable}.
    *
    * @param affectedProjects
    *           the projects for which a rebuild is requested or null
    * @param shell
    *           the parent shell
    * @param message
    *           the message to show to the user
    * @param updater
    *           the updater, which is executed to update the preferences.
    * @return whether the preferences was updated
    */
   public static boolean triggerRebuild(final Set<IProject> affectedProjects,
         final Shell shell, final UserMessage message, final Runnable updater) {

      if (affectedProjects != null && affectedProjects.isEmpty()) {
         // NO projects affected, just update the preferences and return
         updater.run();
         return true;
      }
      if (affectedProjects == null
            && ResourcesPlugin.getWorkspace().getRoot().getProjects().length == 0) {
         // No projects in the workspace
         updater.run();
         return true;
      }

      // Ask the user what to do
      boolean doBuild = false;

      final MessageDialog dialog = new MessageDialog(shell, message.getTitle(),
            null, message.getMessage(), MessageDialog.QUESTION, new String[] {
                  IDialogConstants.YES_LABEL, IDialogConstants.NO_LABEL}, 2);
      final int res = dialog.open();
      if (res == 0) {
         doBuild = true;
      }
      else if (res != 1) {
         // Does not want an update
         return false; // cancel pressed
      }

      // Update and do the build if the user wants to

      updater.run();
      if (doBuild) {
         if (affectedProjects == null) {
            JDTUtil.buildInBackground((IProject) null);
         }
         else {
            for (final IProject project : affectedProjects) {
               JDTUtil.buildInBackground(project);
            }
         }
      }
      return true;
   }

}
