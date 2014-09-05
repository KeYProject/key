package org.key_project.key4eclipse.resources.ui.view;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.log.LogRecord;
import org.key_project.key4eclipse.resources.ui.provider.LogRecordLableProvider;
import org.key_project.key4eclipse.resources.ui.provider.LogRecordLazyContentProvider;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * This view shows the {@link LogRecord}s of KeY projects.
 * @author Martin Hentschel
 */
public class VerificationLogView extends AbstractLinkableViewPart {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.key4eclipse.resources.ui.view.VerificationLogView";

   /**
    * The root control.
    */
   private CTabFolder tabFolder;
   
   /**
    * Maps an {@link IProject} to the {@link CTabItem}.
    */
   private final Map<IProject, CTabItem> tabItems = new HashMap<IProject, CTabItem>();

   /**
    * Maps an {@link IProject} to the {@link TableViewer} which shows its {@link LogRecord}s.
    */
   private final Map<IProject, TableViewer> viewers = new HashMap<IProject, TableViewer>();
   
   /**
    * Listens for resource changes.
    */
   private final IResourceChangeListener resourceChangeListener = new IResourceChangeListener() {
      @Override
      public void resourceChanged(IResourceChangeEvent event) {
         handleResourceChanged(event);
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      tabFolder = new CTabFolder(parent, SWT.FLAT | SWT.BOTTOM);
      updateShownTabs();
      ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceChangeListener);
   }

   /**
    * Updates the shown tabs.
    */
   protected void updateShownTabs() {
      List<IProject> projects = computeProjectsToShow();
      Set<IProject> availableProjects = new HashSet<IProject>(tabItems.keySet());
      for (IProject project : availableProjects) {
         if (!projects.contains(project)) {
            TableViewer viewer = viewers.remove(project);
            if (viewer != null) {
               viewer.getContentProvider().dispose();
               viewer.getLabelProvider().dispose();
            }
            CTabItem item = tabItems.remove(project);
            if (item != null) {
               item.dispose();
            }
         }
      }
      int index = 0;
      for (IProject project : projects) {
         CTabItem tabItem = tabItems.get(project);
         if (tabItem == null) {
            TableColumnLayout tableLayout = new TableColumnLayout();
            Composite viewerComposite = new Composite(tabFolder, SWT.NONE);
            viewerComposite.setLayout(tableLayout);
            TableViewer viewer = new TableViewer(viewerComposite, SWT.BORDER | SWT.FULL_SELECTION | SWT.VIRTUAL | SWT.MULTI);
            viewer.setUseHashlookup(true);
            viewer.getTable().setHeaderVisible(true);
            viewer.getTable().setLinesVisible(true);
            TableViewerColumn kindColumn = new TableViewerColumn(viewer, SWT.NONE);
            kindColumn.getColumn().setText("Kind");
            kindColumn.getColumn().setResizable(true);
            tableLayout.setColumnData(kindColumn.getColumn(), new ColumnWeightData(15));
            TableViewerColumn dateColumn = new TableViewerColumn(viewer, SWT.NONE);
            dateColumn.getColumn().setText("Date");
            dateColumn.getColumn().setResizable(true);
            tableLayout.setColumnData(dateColumn.getColumn(), new ColumnWeightData(15));
            TableViewerColumn durationColumn = new TableViewerColumn(viewer, SWT.NONE);
            durationColumn.getColumn().setText("Duration");
            durationColumn.getColumn().setResizable(true);
            tableLayout.setColumnData(durationColumn.getColumn(), new ColumnWeightData(15));
            TableViewerColumn onlyRequiredProofsColumn = new TableViewerColumn(viewer, SWT.NONE);
            onlyRequiredProofsColumn.getColumn().setText("Build required proofs only");
            onlyRequiredProofsColumn.getColumn().setResizable(true);
            tableLayout.setColumnData(onlyRequiredProofsColumn.getColumn(), new ColumnWeightData(15));
            TableViewerColumn enableThreadingColumn = new TableViewerColumn(viewer, SWT.NONE);
            enableThreadingColumn.getColumn().setText("Enable multithreading");
            enableThreadingColumn.getColumn().setResizable(true);
            tableLayout.setColumnData(enableThreadingColumn.getColumn(), new ColumnWeightData(15));
            TableViewerColumn numberOfThreadsColumn = new TableViewerColumn(viewer, SWT.NONE);
            numberOfThreadsColumn.getColumn().setText("Number of threads");
            numberOfThreadsColumn.getColumn().setResizable(true);
            tableLayout.setColumnData(numberOfThreadsColumn.getColumn(), new ColumnWeightData(15));
            viewer.setContentProvider(new LogRecordLazyContentProvider());
            viewer.setLabelProvider(new LogRecordLableProvider());
            viewer.setInput(project);
            tabItem = new CTabItem(tabFolder, SWT.NONE, index);
            tabItem.setText(project.getName());
            tabItem.setControl(viewerComposite);
            tabItem.setData(project);
            tabItems.put(project, tabItem);
            viewers.put(project, viewer);
            scrollToEnd(viewer);
         }
         index++;
      }
      if (!updateSelectedTab()) { // Try to select tab based on linking
         if (!projects.isEmpty() && tabFolder.getSelection() == null) { // Try to select first tab
            tabFolder.setSelection(0);
         }
      }
   }

   /**
    * Computes the {@link IProject}s to show.
    * @return The {@link IProject}s to show.
    */
   protected List<IProject> computeProjectsToShow() {
      List<IProject> result = new LinkedList<IProject>();
      for (IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
         try {
            if (project.exists() && project.isOpen() && KeYResourcesUtil.isKeYProject(project)) {
               result.add(project);
            }
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      tabFolder.setFocus();
   }
   
   /**
    * When something in the workspace has changed.
    * @param event The {@link IResourceChangeEvent}.
    */
   protected void handleResourceChanged(IResourceChangeEvent event) {
      try {
         final Set<IProject> changedProjects = new HashSet<IProject>();
         if (event.getDelta() != null) {
            event.getDelta().accept(new IResourceDeltaVisitor() {
               @Override
               public boolean visit(IResourceDelta delta) throws CoreException {
                  IResource resource = delta.getResource();
                  if (resource instanceof IFile &&
                      LogManager.getInstance().isLogFile((IFile) resource)) {
                     changedProjects.add(resource.getProject());
                  }
                  return true;
               }
            });
         }
         tabFolder.getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               updateShownTabs();
               if (!changedProjects.isEmpty()) {
                  for (IProject project : changedProjects) {
                     TableViewer viewer = viewers.get(project);
                     viewer.setInput(project);
                     scrollToEnd(viewer);
                  }
               }
            }
         });
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * Scrolls to the {@link TableViewer} to the end.
    * @param viewer The {@link TableViewer} to scroll in.
    */
   protected void scrollToEnd(TableViewer viewer) {
      Table table = viewer.getTable();
      int itemCount = table.getItemCount();
      if (itemCount >= 1) {
         TableItem item = table.getItem(itemCount - 1);
         table.showItem(item);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceChangeListener);
      for (TableViewer viewer : viewers.values()) {
         if (viewer.getContentProvider() != null) {
            viewer.getContentProvider().dispose();
         }
         if (viewer.getLabelProvider() != null) {
            viewer.getLabelProvider().dispose();
         }
      }
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void refreshContentCausedByLinking() {
      updateSelectedTab();
   }
   
   /**
    * Updates the selected tab if linking is enabled.
    * @return {@code true} if selection is defined, {@code false} if no selection was set.
    */
   protected boolean updateSelectedTab() {
      if (isLinkWithBasePart()) {
         CTabItem itemToSelect = null;
         Iterator<IResource> iter = computeLinkedResources().iterator();
         while (itemToSelect == null && iter.hasNext()) {
            itemToSelect = tabItems.get(iter.next().getProject());
         }
         if (itemToSelect != null) {
            tabFolder.setSelection(itemToSelect);
            return true;
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }

   /**
    * Returns the currently shown {@link IProject}.
    * @return The currently shown {@link IProject}.
    */
   public IProject getShownProject() {
      CTabItem item = tabFolder.getSelection();
      if (item != null && item.getData() instanceof IProject) {
         return (IProject) item.getData();
      }
      else {
         return null;
      }
   }
}
