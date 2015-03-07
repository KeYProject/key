package org.key_project.sed.ui.property;

import org.eclipse.debug.core.model.IVariable;
import org.eclipse.ui.views.properties.tabbed.ISection;

/**
 * {@link ISection} implementation to show the basic properties of an {@link IVariable}.
 * @author Martin Hentschel
 */
public class VariablePropertySection extends AbstractVariablePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected IVariableTabContent createContent() {
      return new VariableTabComposite();
   }
}
