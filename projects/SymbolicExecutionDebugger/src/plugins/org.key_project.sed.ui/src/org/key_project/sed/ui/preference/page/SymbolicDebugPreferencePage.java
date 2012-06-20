package org.key_project.sed.ui.preference.page;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * Preference page for the Symbolic Execution Debugger (SED).
 * @author Martin Hentschel
 */
public class SymbolicDebugPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public SymbolicDebugPreferencePage() {
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
