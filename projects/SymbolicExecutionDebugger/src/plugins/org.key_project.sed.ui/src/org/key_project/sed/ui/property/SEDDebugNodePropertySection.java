package org.key_project.sed.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public class SEDDebugNodePropertySection extends AbstractSEDDebugNodePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractSEDDebugNodeTabComposite createContentComposite(Composite parent, int style) {
      return new NodeTabComposite(parent, style, getWidgetFactory());
   }
}