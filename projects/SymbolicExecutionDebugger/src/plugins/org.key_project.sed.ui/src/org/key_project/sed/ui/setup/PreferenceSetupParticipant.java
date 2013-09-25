package org.key_project.sed.ui.setup;

import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.internal.ui.IInternalDebugUIConstants;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.preference.IPreferenceStore;
import org.key_project.util.eclipse.setup.ISetupParticipant;

/**
 * This {@link ISetupParticipant} optimizes the preferences of the Debug API.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class PreferenceSetupParticipant implements ISetupParticipant {
   /**
    * {@inheritDoc}
    */
   @Override
   public void setupWorkspace() {
      getDebugStore().setValue(IInternalDebugUIConstants.PREF_SWITCH_TO_PERSPECTIVE, MessageDialogWithToggle.PROMPT);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void startup() {
      getDebugStore().setDefault(IInternalDebugUIConstants.PREF_SWITCH_TO_PERSPECTIVE, MessageDialogWithToggle.PROMPT);
   }
   
   /**
    * Returns the {@link IPreferenceStore} of the debug API.
    * @return The {@link IPreferenceStore} of the debug API.
    */
   private IPreferenceStore getDebugStore() {
      return DebugUIPlugin.getDefault().getPreferenceStore();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getID() {
      return getClass().getName();
   }
}
