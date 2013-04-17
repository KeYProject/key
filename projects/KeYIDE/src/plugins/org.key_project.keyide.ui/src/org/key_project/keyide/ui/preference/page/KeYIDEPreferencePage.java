package org.key_project.keyide.ui.preference.page;

import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.keyide.ui.util.KeYIDEPreferences;

// TODO: Document class KeYIDEPreferencePage
public class KeYIDEPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public KeYIDEPreferencePage() {
      super(GRID);
      setPreferenceStore(KeYIDEPreferences.getStore());
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
      RadioGroupFieldEditor switchToStateVisualizationPerspectiveEditor = new RadioGroupFieldEditor(KeYIDEPreferences.SWITCH_TO_KEY_PERSPECTIVE, "Open the associated perspective when a KeY proof is requested", 3, new String[][] {{"Always", MessageDialogWithToggle.ALWAYS}, {"Prompt", MessageDialogWithToggle.PROMPT}, {"Never", MessageDialogWithToggle.NEVER}}, getFieldEditorParent(), true);
      addField(switchToStateVisualizationPerspectiveEditor);
   }
}
