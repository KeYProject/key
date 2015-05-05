package org.key_project.util.eclipse.swt;

import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IPageListener;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

/**
 * Instances of this class are used to observe workbench changes in general
 * which includes {@link IWorkbenchWindow}, {@link IWorkbenchPage} and {@link IWorkbenchPart} events.
 * @author Martin Hentschel
 */
public abstract class AbstractWorkbenchPartManager {
   /**
    * Listens for changes.
    */
   private final IWindowListener windowListener = new IWindowListener() {
      @Override
      public void windowOpened(IWorkbenchWindow window) {
         handleWindowOpened(window);
      }
      
      @Override
      public void windowDeactivated(IWorkbenchWindow window) {
         handleWindowDeactivated(window);
      }
      
      @Override
      public void windowClosed(IWorkbenchWindow window) {
         handleWindowClosed(window);
      }
      
      @Override
      public void windowActivated(IWorkbenchWindow window) {
         handleWindowActivated(window);
      }
   };
   
   /**
    * Listens for changes.
    */
   private final IPageListener pageListener = new IPageListener() {
      @Override
      public void pageOpened(IWorkbenchPage page) {
         handlePageOpened(page);
      }
      
      @Override
      public void pageClosed(IWorkbenchPage page) {
         handlePageClosed(page);
      }
      
      @Override
      public void pageActivated(IWorkbenchPage page) {
         handlePageActivated(page);
      }
   };
   
   /**
    * Listens for changes.
    */
   private final IPartListener partListener = new IPartListener() {
      @Override
      public void partOpened(IWorkbenchPart part) {
         handlePartOpened(part);
      }
      
      @Override
      public void partDeactivated(IWorkbenchPart part) {
         handlePartDeactivated(part);
      }
      
      @Override
      public void partClosed(IWorkbenchPart part) {
         handlePartClosed(part);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPart part) {
         handlePartBroughtToTop(part);
      }
      
      @Override
      public void partActivated(IWorkbenchPart part) {
         handlePartActivated(part);
      }
   };
   
   /**
    * Starts observing.
    */
   public void start() {
      PlatformUI.getWorkbench().addWindowListener(windowListener);
      for (IWorkbenchWindow window : PlatformUI.getWorkbench().getWorkbenchWindows()) {
         initWindow(window);
      }
   }

   /**
    * Initializes the given {@link IWorkbenchWindow}.
    * @param window The {@link IWorkbenchWindow} to initialize.
    */
   protected void initWindow(IWorkbenchWindow window) {
      window.addPageListener(pageListener);
      for (IWorkbenchPage page : window.getPages()) {
         initPage(page);
      }
   }

   /**
    * Initializes the given {@link IWorkbenchPage}.
    * @param page The {@link IWorkbenchPage} to initialize.
    */
   protected void initPage(IWorkbenchPage page) {
      page.addPartListener(partListener);
      for (IViewReference reference : page.getViewReferences()) {
         initView(reference);
      }
      for (IEditorReference reference : page.getEditorReferences()) {
         initEditor(reference);
      }
   }

   /**
    * Initializes the given {@link IViewReference}.
    * @param reference The {@link IViewReference} to initialize.
    */
   protected void initView(IViewReference reference) {
   }

   /**
    * Initializes the given {@link IEditorReference}.
    * @param reference The {@link IEditorReference} to initialize.
    */
   protected void initEditor(IEditorReference reference) {
   }

   /**
    * Stops observing.
    */
   public void stop() {
      PlatformUI.getWorkbench().removeWindowListener(windowListener);
      for (IWorkbenchWindow window : PlatformUI.getWorkbench().getWorkbenchWindows()) {
         deinitWindow(window);
      }
   }

   /**
    * Deinitializes the given {@link IWorkbenchWindow}.
    * @param window The {@link IWorkbenchWindow} to initialize.
    */
   protected void deinitWindow(IWorkbenchWindow window) {
      window.removePageListener(pageListener);
      for (IWorkbenchPage page : window.getPages()) {
         deinitPage(page);
      }
   }

   /**
    * Deinitializes the given {@link IWorkbenchPage}.
    * @param page The {@link IWorkbenchPage} to initialize.
    */   
   protected void deinitPage(IWorkbenchPage page) {
      page.removePartListener(partListener);
      for (IViewReference reference : page.getViewReferences()) {
         deinitView(reference);
      }
      for (IEditorReference reference : page.getEditorReferences()) {
         deinitEditor(reference);
      }
   }

   /**
    * Deinitializes the given {@link IViewReference}.
    * @param reference The {@link IViewReference} to initialize.
    */
   protected void deinitView(IViewReference reference) {
   }

   /**
    * Deinitializes the given {@link IEditorReference}.
    * @param reference The {@link IEditorReference} to initialize.
    */
   protected void deinitEditor(IEditorReference reference) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handleWindowOpened(IWorkbenchWindow window) {
      initWindow(window);
   }
   
   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handleWindowClosed(IWorkbenchWindow window) {
      deinitWindow(window);
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handleWindowActivated(IWorkbenchWindow window) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handleWindowDeactivated(IWorkbenchWindow window) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePageOpened(IWorkbenchPage page) {
      initPage(page);
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePageClosed(IWorkbenchPage page) {
      deinitPage(page);
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePageActivated(IWorkbenchPage page) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePartClosed(IWorkbenchPart part) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePartOpened(IWorkbenchPart part) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePartActivated(IWorkbenchPart part) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePartBroughtToTop(IWorkbenchPart part) {
   }

   /**
    * Handles the event.
    * @param window The event.
    */
   protected void handlePartDeactivated(IWorkbenchPart part) {
   }
}