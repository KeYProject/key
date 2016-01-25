package org.key_project.keyide.ui.views;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.IPage;
import org.eclipse.ui.part.IPageBookViewPage;
import org.eclipse.ui.part.MessagePage;
import org.eclipse.ui.part.PageBook;
import org.eclipse.ui.part.PageBookView;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * This {@link PageBookView} shows {@link IGoalPages}s provided by the active
 * {@link IEditorPart} via calling the {@link IEditorPart#getAdapter(Class)}
 * method.
 * 
 * @author Seena Vellaramkalayil
 */
public class GoalsView extends PageBookView {
   /**
    * The id of this view.
    */
   public static final String VIEW_ID = "org.key_project.keyide.ui.view.Goals";
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IPage createDefaultPage(PageBook book) {
      MessagePage page = new MessagePage();
      initPage(page);
      page.createControl(book);
      page.setMessage("No Goals available");
      return page;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected PageRec doCreatePage(IWorkbenchPart part) {
      Object obj = null;
      if (part != null) {
         obj = (IGoalsPage) part.getAdapter(IGoalsPage.class);
      }
      if (obj instanceof IGoalsPage) {
         IGoalsPage page = (IGoalsPage) obj;
         if (page instanceof IPageBookViewPage) {
            initPage((IPageBookViewPage) page);
         }
         page.createControl(getPageBook());
         return new PageRec(part, page);
      }
      return null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void doDestroyPage(IWorkbenchPart part, PageRec pageRecord) {
      IGoalsPage page = (IGoalsPage) pageRecord.page;
      page.dispose();
      pageRecord.dispose();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IWorkbenchPart getBootstrapPart() {
      return WorkbenchUtil.getActiveEditor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isImportant(IWorkbenchPart part) {
      return (part instanceof IEditorPart);
   }
}
