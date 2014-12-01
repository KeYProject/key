package org.key_project.jmlediting.ui.preferencepages;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbenchPropertyPage;

public class JMLProjectPropertiesPage extends PropertyAndPreferencePage
      implements IWorkbenchPropertyPage {

   public JMLProjectPropertiesPage() {
      // TODO Auto-generated constructor stub
   }

   @Override
   protected Control createContents(Composite parent) {
      return null;
   }

   @Override
   protected Control createPreferenceContent(Composite composite) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   protected boolean hasProjectSpecificOptions(IProject project) {
      return false;
   }

   @Override
   protected String getPreferencePageID() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   protected String getPropertyPageID() {
      // TODO Auto-generated method stub
      return null;
   }

}
