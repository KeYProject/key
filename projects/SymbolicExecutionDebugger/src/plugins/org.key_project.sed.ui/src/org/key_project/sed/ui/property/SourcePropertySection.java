package org.key_project.sed.ui.property;

import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show the source associated with an {@link IStackFrame}.
 * @author Martin Hentschel
 */
public class SourcePropertySection extends AbstractPropertySection {
   /**
    * The shown content.
    */
   private SourceTabComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = new SourceTabComposite(parent, SWT.NONE, getWidgetFactory());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      contentComposite.updateContent(getStackFrame());
   }
   
   /**
    * Returns the {@link IStackFrame} to show.
    * @return The {@link IStackFrame} to show or {@code null} if no one should be shown.
    */
   protected IStackFrame getStackFrame() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getStackFrame(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link IStackFrame} if possible.
    * @param object The given {@link Object}.
    * @return The {@link IStackFrame} or {@code null} if conversion is not possible.
    */
   public static IStackFrame getStackFrame(Object object) {
      return object instanceof ISEDDebugNode && // Only in symbolic debug nodes
             object instanceof IStackFrame ? (IStackFrame)object : null;
   }
}