package org.key_project.sed.ui.util;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.debug.internal.ui.views.launch.LaunchView;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.sed.ui.text.AnnotationManager;
import org.key_project.util.eclipse.swt.AbstractWorkbenchPartManager;

/**
 * The {@link LaunchViewManager} is responsible to manage {@link LaunchView} instances.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class LaunchViewManager extends AbstractWorkbenchPartManager {
   /**
    * The only instance of this class.
    */
   private static final LaunchViewManager instance = new LaunchViewManager();

   /**
    * Maps an {@link IDebugView} to its {@link AnnotationManager}.
    */
   private final Map<IDebugView, AnnotationManager> textAnnotationManagerMap = new HashMap<IDebugView, AnnotationManager>();
   
   /**
    * Forbid further instances.
    */
   private LaunchViewManager() {
   }

   /**
    * Returns the only instance.
    * @return The only instance.
    */
   public static LaunchViewManager getInstance() {
      return instance;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void initView(IViewReference reference) {
      super.initView(reference);
      if (IDebugUIConstants.ID_DEBUG_VIEW.equals(reference.getId())) {
         IViewPart view = reference.getView(true);
         if (view instanceof IDebugView) {
            launchViewOpened((IDebugView)view);
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void deinitView(IViewReference reference) {
      super.deinitView(reference);
      if (IDebugUIConstants.ID_DEBUG_VIEW.equals(reference.getId())) {
         IViewPart view = reference.getView(false);
         if (view instanceof IDebugView) {
            launchViewClosed((IDebugView)view);
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePartOpened(IWorkbenchPart part) {
      super.handlePartOpened(part);
      if (part instanceof IDebugView && IDebugUIConstants.ID_DEBUG_VIEW.equals(part.getSite().getId())) {
         launchViewOpened((IDebugView)part);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePartClosed(IWorkbenchPart part) {
      super.handlePartClosed(part);
      if (part instanceof IDebugView && IDebugUIConstants.ID_DEBUG_VIEW.equals(part.getSite().getId())) {
         launchViewClosed((IDebugView)part);
      }
   }
   
   /**
    * When a {@link LaunchView} is opened.
    * @param debugView The opened view.
    */
   protected void launchViewOpened(IDebugView debugView) {
      AnnotationManager manager = textAnnotationManagerMap.get(debugView);
      if (manager == null) {
         manager = new AnnotationManager(debugView);
         textAnnotationManagerMap.put(debugView, manager);
      }
   }
   
   /**
    * When a {@link LaunchView} is closed.
    * @param debugView The closed view.
    */
   protected void launchViewClosed(IDebugView debugView) {
      AnnotationManager manager = textAnnotationManagerMap.remove(debugView);
      if (manager != null) {
         manager.dispose();
      }
   }
}
