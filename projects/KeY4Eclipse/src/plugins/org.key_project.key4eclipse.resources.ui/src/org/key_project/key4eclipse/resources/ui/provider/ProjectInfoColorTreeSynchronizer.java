package org.key_project.key4eclipse.resources.ui.provider;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.events.TreeEvent;
import org.eclipse.swt.events.TreeListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.services.IDisposable;
import org.key_project.key4eclipse.resources.projectinfo.AbstractContractContainer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractTypeContainer;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.IStatusInfo;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.event.IKeYResourcePropertyListener;
import org.key_project.util.eclipse.swt.viewer.ObservableTreeViewer;
import org.key_project.util.eclipse.swt.viewer.event.IViewerUpdateListener;
import org.key_project.util.eclipse.swt.viewer.event.ViewerUpdateEvent;

/**
 * Ensures that the correct foreground colors are shown in an {@link ObservableTreeViewer}
 * showing {@link ProjectInfo}s and its content.
 * @author Martin Hentschel
 */
public class ProjectInfoColorTreeSynchronizer extends AbstractProjectInfoBasedContent implements IDisposable {
   /**
    * The color used for closed proofs.
    */
   public static final RGB COLOR_CLOSED_PROOF = new RGB(0, 117, 0); // JUnit green: 95, 191, 95;
   
   /**
    * The color used for closed proofs.
    */
   public static final RGB COLOR_UNPROVEN_DEPENDENCY = new RGB(0, 0, 170);
   
   /**
    * The color used for open proofs.
    */
   public static final RGB COLOR_PROOF_IN_RECURSION_CYCLE = new RGB(170, 0, 0); // JUnit red: 159, 63, 63
   
   /**
    * The color used for open proofs.
    */
   public static final RGB COLOR_OPEN_PROOF = new RGB(217, 108, 0); // Eclipse warning border: 246, 211, 87
   
   /**
    * The color used for unspecified methods.
    */
   public static final RGB COLOR_UNSPECIFIED = new RGB(110, 110, 110); // JUnit stopped: 120, 120, 120
   
   /**
    * Maps an {@link RGB} to the used {@link Color}.
    */
   private final Map<RGB, Color> colorMap = new HashMap<RGB, Color>();
   
   /**
    * The {@link ObservableTreeViewer} in which colors are set.
    */
   private final ObservableTreeViewer viewer;
   
   /**
    * Listens for changes on {@link #viewer}.
    */
   private final TreeListener treeListener = new TreeListener() {
      @Override
      public void treeExpanded(TreeEvent e) {
         handleTreeExpanded(e);
      }
      
      @Override
      public void treeCollapsed(TreeEvent e) {
         handleTreeCollapsed(e);
      }
   };
   
   /**
    * Listens for changes on {@link #viewer}.
    */
   private final IViewerUpdateListener updateListener = new IViewerUpdateListener() {
      @Override
      public void itemUpdated(ViewerUpdateEvent e) {
         handleItemUpdated(e);
      }
   };
   
   /**
    * Listens for changes on {@link IResource}s.
    */
   private final IResourceChangeListener resourceChangeListener = new IResourceChangeListener() {
      @Override
      public void resourceChanged(IResourceChangeEvent event) {
         handleResourceChanged(event);
      }
   };
   
   /**
    * Listens for changes made by {@link KeYResourcesUtil}.
    */
   private final IKeYResourcePropertyListener resourcePropertyListener = new IKeYResourcePropertyListener() {
      @Override
      public void proofClosedChanged(IFile proofFile, Boolean closed) {
         handleProofClosedChanged(proofFile, closed);
      }

      @Override
      public void proofRecursionCycleChanged(IFile proofFile, List<IFile> cycle) {
         handlProofRecursionCycleChanged(proofFile, cycle);
      }
   };
   
   /**
    * Constructor.
    * @param viewer The {@link ObservableTreeViewer} to show colors in.
    */
   public ProjectInfoColorTreeSynchronizer(List<IProject> input, ObservableTreeViewer viewer) {
      Assert.isNotNull(input);
      Assert.isNotNull(viewer);
      this.viewer = viewer;
      viewer.addViewerUpdateListener(updateListener);
      viewer.getTree().addTreeListener(treeListener);
      for (TreeItem item : viewer.getTree().getItems()) {
         updateColorRecursive(item);
      }
      addProjectInfoListener(input);
      ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceChangeListener);
      KeYResourcesUtil.addKeYResourcePropertyListener(resourcePropertyListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      super.dispose();
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceChangeListener);
      KeYResourcesUtil.removeKeYResourcePropertyListener(resourcePropertyListener);
      viewer.removeViewerUpdateListener(updateListener);
      if (!viewer.getTree().isDisposed()) {
         viewer.getTree().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               viewer.getTree().removeTreeListener(treeListener);
            }
         });
      }
      for (Color color : colorMap.values()) {
         color.dispose();
      }
      colorMap.clear();
   }

   /**
    * When a {@link TreeItem} is expanded.
    * @param e The event.
    */
   protected void handleTreeExpanded(TreeEvent e) {
      TreeItem item = (TreeItem) e.item;
      for (TreeItem child : item.getItems()) {
         updateColor(child);
      }
   }

   /**
    * When a {@link TreeItem} is collapsed.
    * @param e The event.
    */
   protected void handleTreeCollapsed(TreeEvent e) {
   }
   
   /**
    * When a {@link TreeItem} is updated.
    * @param e The event.
    */
   protected void handleItemUpdated(ViewerUpdateEvent e) {
      updateColor((TreeItem)e.getItem());
   }
   
   /**
    * Updates the color recursive in the given {@link TreeItem} and
    * all its child {@link TreeItem}s.
    * @param item The {@link TreeItem} to update.
    */
   protected void updateColorRecursive(TreeItem item) {
      updateColor(item);
      for (TreeItem child : item.getItems()) {
         updateColorRecursive(child);
      }
   }

   /**
    * Updates the {@link Color} of the given data object.
    * @param obj The data object.
    */
   protected void updateColor(final Object obj) {
      viewer.getControl().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            Widget item = viewer.testFindItem(obj);
            if (item instanceof TreeItem) {
               updateColor((TreeItem)item);
            }
         }
      });
   }

   /**
    * Updates the {@link Color}s of the given {@link TreeItem}.
    * @param item The {@link TreeItem} to update its colors.
    */
   protected void updateColor(TreeItem item) {
      Object data = item.getData();
      if (data instanceof IProject) {
         data = ProjectInfoManager.getInstance().getProjectInfo((IProject)data);
      }
      if (data instanceof IStatusInfo) {
         IStatusInfo info = (IStatusInfo) data;
         if (info.isPartOfRecursionCycle()) {
            item.setForeground(createColor(COLOR_PROOF_IN_RECURSION_CYCLE, viewer.getControl().getDisplay()));
         }
         else if (info.hasOpenProof()) {
            item.setForeground(createColor(COLOR_OPEN_PROOF, viewer.getControl().getDisplay()));
         }
         else if (info.isUnspecified()) {
            item.setForeground(createColor(COLOR_UNSPECIFIED, viewer.getControl().getDisplay()));
         }
         else if (info.hasUnprovenDependencies()) {
            item.setForeground(createColor(COLOR_UNPROVEN_DEPENDENCY, viewer.getControl().getDisplay()));
         }
         else {
            item.setForeground(createColor(COLOR_CLOSED_PROOF, viewer.getControl().getDisplay()));
         }
      }
   }
   
   /**
    * Returns the {@link Color} instance for the given {@link RGB} value.
    * @param rgb The {@link RGB} value.
    * @param display The {@link Display} in which the {@link Color} will be used.
    * @return The {@link Color} with the specified {@link RGB}.
    */
   protected Color createColor(RGB rgb, Display display) {
      Color color = colorMap.get(rgb);
      if (color == null) {
         color = new Color(display, rgb);
         colorMap.put(rgb, color);
      }
      return color;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleTypeAdded(final AbstractTypeContainer tcInfo, final TypeInfo type, final int index) {
      updateObjectAndParents(tcInfo);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleTypesRemoved(final AbstractTypeContainer tcInfo, final Collection<TypeInfo> types) {
      updateParents(types);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleMethodAdded(final TypeInfo type, final MethodInfo method, final int index) {
      updateObjectAndParents(type);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleMethodsRemoved(final TypeInfo type, final Collection<MethodInfo> methods) {
      updateParents(methods);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleObserverFunctionAdded(final TypeInfo type, final ObserverFunctionInfo observerFunction, final int index) {
      updateObjectAndParents(type);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleObserFunctionsRemoved(final TypeInfo type, final Collection<ObserverFunctionInfo> observerFunctions) {
      updateParents(observerFunctions);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleContractAdded(final AbstractContractContainer cc, final ContractInfo contract, final int index) {
      updateObjectAndParents(cc);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleContractsRemoved(final AbstractContractContainer cc, final Collection<ContractInfo> contracts) {
      updateParents(contracts);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePackageAdded(final ProjectInfo projectInfo, final PackageInfo packageInfo, final int index) {
      updateObjectAndParents(projectInfo);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePackagesRemoved(final ProjectInfo projectInfo, final Collection<PackageInfo> packages) {
      updateParents(packages);
   }

   /**
    * When some {@link IResource}s have changed.
    * @param event The {@link IResourceChangeEvent}.
    */
   protected void handleResourceChanged(IResourceChangeEvent event) {
      handleResourceDelta(event.getDelta());
   }

   /**
    * Works with the given {@link IResourceDelta}.
    * @param delta The {@link IResourceDelta} to work with.
    */
   protected void handleResourceDelta(IResourceDelta delta) {
      if (delta != null) {
         updateModelElementsOfResource(delta.getResource());
         for (IResourceDelta childDelta : delta.getAffectedChildren()) {
            handleResourceDelta(childDelta);
         }
      }
   }

   /**
    * The proof closed persistent property has changed via
    * {@link KeYResourcesUtil#setProofClosed(IFile, Boolean)}.
    * @param proofFile The changed proof file.
    * @param closed The new closed state.
    */
   protected void handleProofClosedChanged(IFile proofFile, Boolean closed) {
      updateModelElementsOfResource(proofFile);
   }

   /**
    * The proof recursion cycle persistent property has changed via
    * {@link KeYResourcesUtil#setProofRecursionCycle(IFile, List)}.
    * @param proofFile The changed proof file.
    * @param cycle The new recursion cycle or {@code null} if not part of a cycle.
    */
   protected void handlProofRecursionCycleChanged(IFile proofFile, List<IFile> cycle) {
      updateModelElementsOfResource(proofFile);
   }
   
   /**
    * When a resource has changed.
    * @param resource The changed {@link IResource}.
    */
   protected void updateModelElementsOfResource(IResource resource) {
      Set<Object> elements = getModelElements(resource);
      if (elements != null) {
         for (Object element : elements) {
            updateObjectAndParents(element);
         }
      }
   }

   /**
    * Updates the color of all parents of all given {@link Object}s.
    * @param objects The {@link Object}s to update their parents.
    */
   protected void updateParents(Collection<?> objects) {
      for (Object obj : objects) {
         updateObjectAndParents(ProjectInfoManager.getParent(obj));
      }
   }

   /**
    * Updates the element and all its parents.
    * @param element The element to update.
    */
   protected void updateObjectAndParents(Object element) {
      while (element != null) {
         if (element instanceof ProjectInfo) {
            element = getProject((ProjectInfo) element);
         }
         updateColor(element);
         element = ProjectInfoManager.getParent(element);
      }
   }
}
