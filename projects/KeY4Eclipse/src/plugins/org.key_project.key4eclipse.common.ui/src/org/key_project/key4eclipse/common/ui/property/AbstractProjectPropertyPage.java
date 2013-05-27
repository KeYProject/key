package org.key_project.key4eclipse.common.ui.property;

import org.eclipse.core.resources.IProject;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * Provides a basic implementation for a {@link PropertyPage} which works on an {@link IProject}.
 * @author Martin Hentschel
 */
public abstract class AbstractProjectPropertyPage extends PropertyPage implements IWorkbenchPropertyPage {
   /**
    * Returns the {@link IProject} that is currently configured.
    * @return The {@link IProject} to configure.
    */
   protected IProject getProject() {
       if (getElement() != null) {
           return (IProject)getElement().getAdapter(IProject.class);
       }
       else {
           return null;
       }
   }
}
