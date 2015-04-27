package org.key_project.util.eclipse.swt.view;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;

/**
 * <p>
 * A {@link TabbedPropertySheetPage} which ensures that always the content
 * according to the selection of the parent {@link IWorkbenchPart} is shown.
 * </p>
 * <p>
 * This class is required to fix the behavior in Eclipse 4 where the
 * selection is not automatically updated when the parent {@link IWorkbenchPart}
 * is not active.
 * </p>
 * @author Martin Hentschel
 */
public class ParentBasedTabbedPropertySheetPage extends TabbedPropertySheetPage {
   /**
    * The parent {@link IWorkbenchPart}.
    */
   private final IWorkbenchPart parentPart;
   
   /**
    * Constructor.
    * @param parentPart the parent {@link IWorkbenchPart}.
    * @param tabbedPropertySheetPageContributor the tabbed property sheet page contributor.     
    */
   public ParentBasedTabbedPropertySheetPage(IWorkbenchPart parentPart, 
                                             ITabbedPropertySheetPageContributor tabbedPropertySheetPageContributor) {
      super(tabbedPropertySheetPageContributor);
      this.parentPart = parentPart;
   }

   /**
    * Constructor.
    * @param parentPart the parent {@link IWorkbenchPart}.
    * @param tabbedPropertySheetPageContributor the tabbed property sheet page contributor.     
    * @param showTitleBar boolean indicating if the title bar should be shown; default value is <code>true</code>   
    */
   public ParentBasedTabbedPropertySheetPage(IWorkbenchPart parentPart, 
                                             ITabbedPropertySheetPageContributor tabbedPropertySheetPageContributor, 
                                             boolean showTitleBar) {
      super(tabbedPropertySheetPageContributor, showTitleBar);
      this.parentPart = parentPart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      super.createControl(parent);
      selectionChanged(parentPart, parentPart.getSite().getSelectionProvider().getSelection());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePartActivated(IWorkbenchPart part) {
      super.handlePartActivated(part);
      if (parentPart == part) {
         selectionChanged(parentPart, parentPart.getSite().getSelectionProvider().getSelection());
      }
   }
}
