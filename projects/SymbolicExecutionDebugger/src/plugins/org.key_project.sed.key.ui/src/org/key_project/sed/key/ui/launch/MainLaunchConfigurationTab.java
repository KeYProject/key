package org.key_project.sed.key.ui.launch;

import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.key.ui.util.KeYSEDImages;

/**
 * {@link AbstractLaunchConfigurationTab} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class MainLaunchConfigurationTab extends AbstractTabbedPropertiesAndLaunchConfigurationTab {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Main";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractTabbedPropertiesAndLaunchConfigurationTabComposite createContentComposite(Composite parent, int style) {
      return new MainLaunchConfigurationComposite(parent, style, this, null);
   }
}
