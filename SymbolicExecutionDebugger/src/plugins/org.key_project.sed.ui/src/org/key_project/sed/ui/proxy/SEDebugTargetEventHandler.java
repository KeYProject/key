package org.key_project.sed.ui.proxy;

import java.util.List;

import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelDelta;
import org.eclipse.debug.internal.ui.viewers.model.provisional.ModelDelta;
import org.eclipse.debug.internal.ui.viewers.update.DebugEventHandler;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.ui.util.LogUtil;

/**
 * An {@link DebugEventHandler} handling {@link ISEDebugTarget}s.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDebugTargetEventHandler extends DebugEventHandler {
   /**
    * Constructor.
    * @param proxy The {@link SEDebugTargetProxy} in which this {@link DebugEventHandler} is used.
    */
   public SEDebugTargetEventHandler(SEDebugTargetProxy proxy) {
      super(proxy);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected SEDebugTargetProxy getModelProxy() {
      return (SEDebugTargetProxy)super.getModelProxy();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean handlesEvent(DebugEvent event) {
      return event.getSource() instanceof ISEDebugTarget;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleChange(DebugEvent event) {
      int flags = IModelDelta.STATE;
      if (event.getDetail() == DebugEvent.CONTENT) {
         flags = flags | IModelDelta.CONTENT;
      }
      fireDelta((ISEDebugTarget) event.getSource(), flags);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleCreate(DebugEvent event) {
        fireDelta((ISEDebugTarget) event.getSource(), IModelDelta.EXPAND);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleResume(DebugEvent event) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleSuspend(DebugEvent event) {
      fireDelta((ISEDebugTarget) event.getSource(), IModelDelta.CONTENT | IModelDelta.STATE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleTerminate(DebugEvent event) {
      fireDelta((ISEDebugTarget) event.getSource(), IModelDelta.CONTENT | IModelDelta.STATE | IModelDelta.UNINSTALL);
   }

   /**
    * Creates and fires an {@link IModelDelta}.
    * @param target The observed {@link ISEDebugTarget} which has changed.
    * @param targetFlags The flags to fire.
    */
   protected void fireDelta(ISEDebugTarget target, int targetFlags) {
      SEDebugTargetProxy modelProxy = getModelProxy();
      if (modelProxy != null) {
         ILaunchManager manager = DebugPlugin.getDefault().getLaunchManager();
         ModelDelta delta = new ModelDelta(manager, IModelDelta.NO_CHANGE);
         try {
            modelProxy.fillModelDeltaToUpdateTarget(manager, delta, targetFlags);
            List<ISENode> leafsToSelect = modelProxy.collectLeafsToSelect(target);
            modelProxy.fireModelChangedWithMultiSelect(delta, leafsToSelect);
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
            modelProxy.fireModelChanged(delta);
         }
      }
   }
}
