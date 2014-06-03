package org.key_project.sed.ui.proxy;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelDelta;
import org.eclipse.debug.internal.ui.viewers.model.provisional.ModelDelta;
import org.eclipse.debug.internal.ui.viewers.update.DebugEventHandler;
import org.eclipse.debug.internal.ui.viewers.update.DebugTargetProxy;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * The {@link DebugTargetProxy} used for {@link ISEDDebugTarget}s.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDDebugTargetProxy extends DebugTargetProxy {
   /**
    * The handled {@link ISEDDebugTarget}.
    */
   private final ISEDDebugTarget target;

   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} to handle.
    */
   public SEDDebugTargetProxy(ISEDDebugTarget target) {
      super(target);
      this.target = target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected DebugEventHandler[] createEventHandlers() {
      return new DebugEventHandler[] { new SEDDebugTargetEventHandler(this), 
                                       new SEDThreadEventHandler(this) 
                                      };
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ModelDelta getNextSuspendedThreadDelta(IThread currentThread, boolean reverse) {
      ModelDelta delta = super.getNextSuspendedThreadDelta(currentThread, reverse);
      try {
         if (delta == null) {
            ILaunchManager manager = DebugPlugin.getDefault().getLaunchManager();
            delta = new ModelDelta(manager, IModelDelta.NO_CHANGE);
            List<ISEDDebugNode> leafsToSelect = collectLeafsToSelect(target);
            fillModelDeltaToSelectLeafs(manager, delta, IModelDelta.EXPAND, leafsToSelect);
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
      return delta;
   }
   
   /**
    * Collects all leafs on all {@link ISEDThread}s of the given {@link ISEDDebugTarget}.
    * @param target The {@link ISEDDebugTarget} to collect its leaf.
    * @return All leafs collected via {@link ISEDThread#getLeafsToSelect()}.
    * @throws DebugException Occurred Exceptions.
    */
   protected List<ISEDDebugNode> collectLeafsToSelect(ISEDDebugTarget target) throws DebugException {
      List<ISEDDebugNode> leafsToSelect = new LinkedList<ISEDDebugNode>();
      for (ISEDThread thread : target.getSymbolicThreads()) {
         CollectionUtil.addAll(leafsToSelect, thread.getLeafsToSelect());
      }
      return leafsToSelect;
   }
   
   /**
    * Fills the given {@link ModelDelta}.
    * @param manager The {@link ILaunchManager} to use.
    * @param delta The {@link ModelDelta} to fill.
    * @param targetFlags The flags to use for the {@link ISEDDebugTarget}.
    * @param leafsToSelect The {@link ISEDDebugNode}s to select.
    * @throws DebugException Occurred Exceptions.
    */
   // TODO: Fix in combination with set visualization
   // TODO: Change to single selection since multi selection is not possible
   protected void fillModelDeltaToSelectLeafs(ILaunchManager manager,
                                              ModelDelta delta, 
                                              int targetFlags,
                                              List<ISEDDebugNode> leafsToSelect) throws DebugException {
      // Add launch
      ILaunch launch = target.getLaunch();
ISEDDebugNode leaf = !leafsToSelect.isEmpty() ? leafsToSelect.get(0) : null;
if (leaf != null) {
//      for (ISEDDebugNode leaf : leafsToSelect) {
         int launchIndex = indexOf(manager.getLaunches(), launch);
         ModelDelta node = delta.addNode(launch, launchIndex, IModelDelta.NO_CHANGE, launch.getChildren().length);
         // Collect all children on path from thread to leaf
         List<Object> parents = new LinkedList<Object>();
         Object parent = leaf;
         while (!(parent instanceof ISEDThread)) {
            parents.add(0, parent);
            parent = SEDUIUtil.getParent(parent);
         }
         parent = leaf.getThread();
         Object[] parentChildren = SEDUIUtil.getChildren(parent);
         // Add target
         int targetIndex = indexOf(launch.getChildren(), target);
         node = node.addNode(target, targetIndex, targetFlags, target.getSymbolicThreads().length);
         // Add thread
         int threadIndex = 0;
         int threadFlags = parents.isEmpty() ? IModelDelta.NO_CHANGE | IModelDelta.SELECT : IModelDelta.NO_CHANGE | IModelDelta.EXPAND;
         node = node.addNode(parent, threadIndex, threadFlags, parentChildren.length);
//         // Add collected children on path from thread to leaf
//         Iterator<Object> parentIter = parents.iterator();
//         while (parentIter.hasNext()) {
//            parent = parentIter.next();
//            int parentIndex = indexOf(parentChildren, parent);
//            parentChildren = SEDUIUtil.getChildren(parent);
//            int parentFlags = parentIter.hasNext() ? IModelDelta.NO_CHANGE | IModelDelta.EXPAND : IModelDelta.NO_CHANGE | IModelDelta.SELECT;
//            node = node.addNode(parent, parentIndex, parentFlags, parentChildren.length);
//         }
      }
   }
}
