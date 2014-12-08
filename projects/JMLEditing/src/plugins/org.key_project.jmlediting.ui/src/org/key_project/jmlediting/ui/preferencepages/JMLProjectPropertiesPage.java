package org.key_project.jmlediting.ui.preferencepages;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbenchPropertyPage;

/**
 * This class provides the top level entry for JML preferences in properties or
 * preference windows. Currently it does not contain anything.
 *
 * @author Moritz Lichter
 *
 */
@SuppressWarnings("restriction")
public class JMLProjectPropertiesPage extends PropertyAndPreferencePage
implements IWorkbenchPropertyPage {

   /**
    * Creates a new instance.
    */
   public JMLProjectPropertiesPage() {
   }

   @Override
   protected Control createContents(final Composite parent) {
      return null;
   }

   @Override
   protected Control createPreferenceContent(final Composite composite) {
      return null;
   }

   @Override
   protected boolean hasProjectSpecificOptions(final IProject project) {
      return false;
   }

   @Override
   protected String getPreferencePageID() {
      return null;
   }

   @Override
   protected String getPropertyPageID() {
      return null;
   }

}
