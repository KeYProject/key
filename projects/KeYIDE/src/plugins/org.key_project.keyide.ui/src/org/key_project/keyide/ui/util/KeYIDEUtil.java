package org.key_project.keyide.ui.util;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.ui.IWorkbenchPage;
import org.key_project.keyide.ui.visualization.VisualizationPreferences;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class KeYIDEUtil {
   /**
    * Searches a {@link FunctionalOperationContract} with the given name.
    * @param operationContracts The available {@link FunctionalOperationContract} to search in.
    * @param contractName The name of the {@link FunctionalOperationContract} to search.
    * @return The found {@link FunctionalOperationContract} or {@code null} if no one was found.
    */
   public static FunctionalOperationContract findContract(ImmutableSet<FunctionalOperationContract> operationContracts, 
                                                          final String contractName) {
       return CollectionUtil.search(operationContracts, new IFilter<FunctionalOperationContract>() {
           @Override
           public boolean select(FunctionalOperationContract element) {
               return element != null && ObjectUtil.equals(element.getName(), contractName);
           }
       });
   }
   
   
   /**
    * Checks if a perspective switch to the state visualization perspective should be done.
    * @param activePage The currently active {@link IWorkbenchPage}.
    * @return {@code true} switch to state visualization perspective, {@code false} stay in current perspective.
    */
   public static boolean shouldSwitchToKeyPerspective(IWorkbenchPage activePage) {
      boolean switchPerspective = false;
      // Check if a different perspective is currently opened.
      if (!WorkbenchUtil.isPerspectiveOpen("org.key_project.keyide.ui.perspectives", activePage)) {
         String option = VisualizationPreferences.getSwitchToKeyPerspective();
         if (MessageDialogWithToggle.ALWAYS.equals(option)) {
            switchPerspective = true;
         }
         else if (MessageDialogWithToggle.NEVER.equals(option)) {
            switchPerspective = false;
         }
         else {
            MessageDialogWithToggle dialog = MessageDialogWithToggle.openYesNoQuestion(activePage.getActivePart().getSite().getShell(), 
                                                                                       "Confirm Perspective Switch", 
                                                                                       "The Proof management is associated with the " + WorkbenchUtil.getPerspectiveName("org.key_project.keyide.ui.perspectives") + " perspective.\n\nDo you want to open this perspective now?", 
                                                                                       null, 
                                                                                       false, 
                                                                                       VisualizationPreferences.getStore(), 
                                                                                       VisualizationPreferences.SWITCH_TO_KEY_PERSPECTIVE);
            switchPerspective = (dialog.getReturnCode() == IDialogConstants.YES_ID);
         }
      }
      return switchPerspective;
   }

}
