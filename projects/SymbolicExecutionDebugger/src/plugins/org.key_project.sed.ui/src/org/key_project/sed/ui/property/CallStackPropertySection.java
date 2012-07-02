package org.key_project.sed.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * {@link ISection} implementation to show the call stack of an {@link ISEDDebugNode}
 * which is provided via {@link ISEDDebugNode#getCallStack()}.
 * @author Martin Hentschel
 */
public class CallStackPropertySection extends AbstractSEDDebugNodePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractSEDDebugNodeTabComposite createContentComposite(Composite parent, int style) {
      return new CallStackTabComposite(parent, style, getWidgetFactory());
   }
}