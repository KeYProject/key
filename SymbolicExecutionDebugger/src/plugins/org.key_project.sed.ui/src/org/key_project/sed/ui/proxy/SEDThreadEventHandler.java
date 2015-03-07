package org.key_project.sed.ui.proxy;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelDelta;
import org.eclipse.debug.internal.ui.viewers.model.provisional.ModelDelta;
import org.eclipse.debug.internal.ui.viewers.update.DebugEventHandler;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * An {@link DebugEventHandler} handling {@link ISEDThread}s.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDThreadEventHandler extends DebugEventHandler {
   /**
    * Constructor.
    * @param proxy The {@link SEDDebugTargetProxy} in which this {@link DebugEventHandler} is used.
    */
   public SEDThreadEventHandler(SEDDebugTargetProxy proxy) {
      super(proxy);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected SEDDebugTargetProxy getModelProxy() {
      return (SEDDebugTargetProxy)super.getModelProxy();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean handlesEvent(DebugEvent event) {
      return event.getSource() instanceof ISEDThread;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleSuspend(DebugEvent event) {
      fireDelta((ISEDThread) event.getSource());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleSuspendTimeout(DebugEvent event) {
      fireDelta((ISEDThread) event.getSource());
   }
   
   /**
    * Creates and fires an {@link IModelDelta}.
    * @param thread The observed {@link ISEDThread} which has changed.
    */
   protected void fireDelta(ISEDThread thread) {
      SEDDebugTargetProxy modelProxy = getModelProxy();
      if (modelProxy != null) {
         ILaunchManager manager = DebugPlugin.getDefault().getLaunchManager();
         ModelDelta delta = new ModelDelta(manager, IModelDelta.CONTENT);
         try {
            List<ISEDDebugNode> leafsToSelect = new LinkedList<ISEDDebugNode>();
            CollectionUtil.addAll(leafsToSelect, thread.getLeafsToSelect());
            modelProxy.fillModelDeltaToUpdateTarget(manager, delta, IModelDelta.NO_CHANGE);
            modelProxy.fireModelChangedWithMultiSelect(delta, leafsToSelect);
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
            modelProxy.fireModelChanged(delta);
         }
      }
   }
}
