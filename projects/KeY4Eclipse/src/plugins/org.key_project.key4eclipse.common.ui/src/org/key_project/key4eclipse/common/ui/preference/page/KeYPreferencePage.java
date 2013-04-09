package org.key_project.key4eclipse.common.ui.preference.page;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * Preference page for KeY.
 * @author Martin Hentschel
 */
public class KeYPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public KeYPreferencePage() {
      super(GRID);
      noDefaultAndApplyButton();
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
      // Maybe this page is filled in the future with real content, now it is only a category in the tree.
   }
}
