package org.key_project.sed.ui.property;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public class SEDDebugNodePropertySection extends AbstractPropertySection {
   /**
    * The shown content.
    */
   private NodeTabComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = new NodeTabComposite(parent, SWT.NONE, getWidgetFactory());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      contentComposite.updateContent(getDebugNode());
   }
   
   /**
    * Returns the {@link ISEDDebugNode} to show.
    * @return The {@link ISEDDebugNode} to show or {@code null} if no one should be shown.
    */
   protected ISEDDebugNode getDebugNode() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugNode(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link ISEDDebugNode} if possible.
    * @param object The given {@link Object}.
    * @return The {@link ISEDDebugNode} or {@code null} if conversion is not possible.
    */
   public static ISEDDebugNode getDebugNode(Object object) {
      return object instanceof ISEDDebugNode ? (ISEDDebugNode)object : null;
   }
}