package org.key_project.sed.key.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.launch.AbstractTabbedPropertiesAndLaunchConfigurationTabComposite;
import org.key_project.sed.key.ui.launch.KeYPerformanceLaunchConfigurationTabComposite;

/**
 * {@link ISection} implementation to show the properties of {@link KeYDebugTarget}s
 * in an {@link KeYPerformanceLaunchConfigurationTabComposite} instance.
 * @author Martin Hentschel
 */
public class PerformanceKeYDebugTargetPropertySection extends AbstractKeYDebugTargetPropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractTabbedPropertiesAndLaunchConfigurationTabComposite createContentComposite(Composite parent, int style) {
      return new KeYPerformanceLaunchConfigurationTabComposite(parent, style, null, getWidgetFactory());
   }
}