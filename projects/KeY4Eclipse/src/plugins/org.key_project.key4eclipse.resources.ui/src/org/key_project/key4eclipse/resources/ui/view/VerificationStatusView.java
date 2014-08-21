package org.key_project.key4eclipse.resources.ui.view;

import java.io.File;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.browser.LocationEvent;
import org.eclipse.swt.browser.LocationListener;
import org.eclipse.swt.browser.StatusTextEvent;
import org.eclipse.swt.browser.StatusTextListener;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.dnd.Clipboard;
import org.eclipse.swt.dnd.HTMLTransfer;
import org.eclipse.swt.dnd.TextTransfer;
import org.eclipse.swt.dnd.Transfer;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.eclipse.ui.part.EditorPart;
import org.key_project.key4eclipse.common.ui.util.KeYImages;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.key4eclipse.resources.io.ProofMetaFileAssumption;
import org.key_project.key4eclipse.resources.projectinfo.AbstractContractContainer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractTypeContainer;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo.TacletOptionIssues;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;
import org.key_project.key4eclipse.resources.projectinfo.event.IProjectInfoListener;
import org.key_project.key4eclipse.resources.ui.provider.ProjectInfoColorTreeSynchronizer;
import org.key_project.key4eclipse.resources.ui.provider.ProjectInfoLabelProvider;
import org.key_project.key4eclipse.resources.ui.provider.ProjectInfoLazyTreeContentProvider;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.event.IKeYResourcePropertyListener;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.CustomProgressBar;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.AbstractWorkbenchPartBasedView;
import org.key_project.util.eclipse.swt.viewer.ObservableTreeViewer;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.ChoiceSelector.ChoiceEntry;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * This {@link IViewPart} shows the verification status.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class VerificationStatusView extends AbstractWorkbenchPartBasedView {
   /**
    * The unique ID of this view.
    */
   public static final String ID = "org.key_project.key4eclipse.resources.ui.view.VerificationStatusView";
   
   /**
    * The protocol used to link {@link ResourcesPlugin}s in the Eclipse workspace.
    */
   private static final String PROTOCOL_RESOURCE = "resource:";

   /**
    * The protocol used to link to {@link File}s in the local file system.
    */
   private static final String PROTOCOL_FILE_PREFIX = "file:/";

   /**
    * The root {@link Composite} which contains all shown content.
    */
   private Composite rootComposite;
   
   /**
    * Shows the proof progress.
    */
   private CustomProgressBar proofProgressBar;
   
   /**
    * Shows the verification progress.
    */
   private CustomProgressBar specificationProgressBar;
   
   /**
    * Shows the project structure and the individual proof and specification stati.
    */
   private ObservableTreeViewer treeViewer;
   
   /**
    * Content provider of {@link #treeViewer}.
    */
   private ProjectInfoLazyTreeContentProvider contentProvider;
   
   /**
    * Label provider of {@link #treeViewer}.
    */
   private ProjectInfoLabelProvider labelProvider;
   
   /**
    * Sets the colors in {@link #treeViewer}.
    */
   private ProjectInfoColorTreeSynchronizer colorSynchronizer;
   
   /**
    * The currently shown {@link IProject}s.
    */
   private List<IProject> projects;
   
   /**
    * The currently shown {@link ProjectInfo}s of {@link #projects}.
    */
   private Map<IProject, ProjectInfo> projectInfos;
   
   /**
    * Listens for changes on {@link #projectInfos}.
    */
   private final IProjectInfoListener projectInfoListener = new IProjectInfoListener() {
      @Override
      public void typesRemoved(AbstractTypeContainer tcInfo, Collection<TypeInfo> types) {
         handleTypesRemoved(tcInfo, types);
      }
      
      @Override
      public void typeAdded(AbstractTypeContainer tcInfo, TypeInfo type, int index) {
         handleTypeAdded(tcInfo, type, index);
      }

      @Override
      public void methodAdded(TypeInfo type, MethodInfo method, int index) {
         handleMethodAdded(type, method, index);
      }

      @Override
      public void methodsRemoved(TypeInfo type, Collection<MethodInfo> methods) {
         handleMethodsRemoved(type, methods);
      }

      @Override
      public void observerFunctionAdded(TypeInfo type, ObserverFunctionInfo observerFunction, int index) {
         handleObserverFunctionAdded(type, observerFunction, index);
      }

      @Override
      public void obserFunctionsRemoved(TypeInfo type, Collection<ObserverFunctionInfo> observerFunctions) {
         handleObserFunctionsRemoved(type, observerFunctions);
      }

      @Override
      public void contractAdded(AbstractContractContainer cc, ContractInfo contract, int index) {
         handleContractAdded(cc, contract, index);
      }

      @Override
      public void contractsRemoved(AbstractContractContainer cc, Collection<ContractInfo> contracts) {
         handleContractsRemoved(cc, contracts);
      }

      @Override
      public void packageAdded(ProjectInfo projectInfo, PackageInfo packageInfo, int index) {
         handlePackageAdded(projectInfo, packageInfo, index);
      }

      @Override
      public void packagesRemoved(ProjectInfo projectInfo, Collection<PackageInfo> packages) {
         handlePackagesRemoved(projectInfo, packages);
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
    * The color for cyclic proofs.
    */
   private Color cyclicProofsColor;
   
   /**
    * The color for open proofs.
    */
   private Color openProofColor;

   /**
    * The color for unspecified elements.
    */
   private Color unspecifiedColor;

   /**
    * The color for unproven dependencies.
    */
   private Color unprovenDependencyColor;

   /**
    * The color for closed proofs.
    */
   private Color closedProofColor;
   
   /**
    * The {@link Browser} which shows the HTML report.
    */
   private Browser reportBrowser;
   
   /**
    * The currently selected text in {@link #reportBrowser}.
    */
   private String selectedReportBrowserText;

   /**
    * The link with editor/view state.
    */
   private State linkState;
   
   /**
    * Listens for changes on {@link #linkState}.
    */
   private final IStateListener stateListener = new IStateListener() {
      @Override
      public void handleStateChange(State state, Object oldValue) {
         updateShownContent();
      }
   };
   
   /**
    * The base {@link IWorkbenchPart} for which the content will be shown
    * if {@link #linkState} is selected.
    */
   private IWorkbenchPart basePart;
   
   /**
    * Listens for changes on {@link #basePart}.
    */
   private final IPropertyListener basePartListener = new IPropertyListener() {
      @Override
      public void propertyChanged(Object source, int propId) {
         handleBasePartPropertyChanged(source, propId);
      }
   };

   /**
    * Listens for changes on {@link #basePart}.
    */
   private final ISelectionChangedListener basePartSelectionChangedListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleBasePartSelectionChanged(event);
      }
   };
   
   /**
    * The currently running {@link Job}.
    */
   private Job activeJob;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewSite site) throws PartInitException {
      super.init(site);
      ICommandService service = (ICommandService)PlatformUI.getWorkbench().getService(ICommandService.class);
      Command linkCmd = service.getCommand("org.key_project.key4eclipse.resources.ui.LinkWithWorkbenchPartCommand");
      if (linkCmd != null) {
         linkState = linkCmd.getState(RegistryToggleState.STATE_ID);
         if (linkState != null) {
            linkState.addListener(stateListener);
         }
      }
      basePart = site.getPage().getActivePart();
      if (basePart instanceof EditorPart) {
         ((EditorPart) basePart).addPropertyListener(basePartListener);
      }
      if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
         basePart.getSite().getSelectionProvider().addSelectionChangedListener(basePartSelectionChangedListener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      rootComposite = new Composite(parent, SWT.NONE);
      GridLayout rootLayout = new GridLayout(1, false);
      rootLayout.verticalSpacing = 0;
      rootComposite.setLayout(rootLayout);
      // progressComposite
      Composite progressComposite = new Composite(rootComposite, SWT.NONE);
      progressComposite.setLayout(new GridLayout(4, false));
      progressComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      Label proofLabel = new Label(progressComposite, SWT.NONE);
      proofLabel.setText("Proofs");
      proofProgressBar = new CustomProgressBar(progressComposite, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF, ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
      proofProgressBar.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      Label specificationLabel = new Label(progressComposite, SWT.NONE);
      specificationLabel.setText("Specifications");
      specificationProgressBar = new CustomProgressBar(progressComposite, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
      specificationProgressBar.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      // tabFolder
      CTabFolder tabFolder = new CTabFolder(rootComposite, SWT.FLAT | SWT.BOTTOM);
      tabFolder.setLayoutData(new GridData(GridData.FILL_BOTH));
      // treeViewrLegendComposite
      Composite treeViewrLegendComposite = new Composite(tabFolder, SWT.NONE);
      GridLayout treeViewrLegendCompositeLayout = new GridLayout(1, false);
      treeViewrLegendCompositeLayout.verticalSpacing = 0;
      treeViewrLegendCompositeLayout.marginTop = 0;
      treeViewrLegendCompositeLayout.marginBottom = 0;
      treeViewrLegendCompositeLayout.marginLeft = 0;
      treeViewrLegendCompositeLayout.marginRight = 0;
      treeViewrLegendCompositeLayout.horizontalSpacing = 0;
      treeViewrLegendCompositeLayout.marginWidth = 0;
      treeViewrLegendComposite.setLayout(treeViewrLegendCompositeLayout);
      // proofAndSpecsTabItem
      CTabItem proofAndSpecsTabItem = new CTabItem(tabFolder, SWT.NONE);
      proofAndSpecsTabItem.setText("&Proofs and Specifications");
      proofAndSpecsTabItem.setControl(treeViewrLegendComposite);
      tabFolder.setSelection(proofAndSpecsTabItem);
      // treeViewer
      treeViewer = new ObservableTreeViewer(treeViewrLegendComposite, SWT.BORDER | SWT.MULTI | SWT.VIRTUAL);
      treeViewer.setUseHashlookup(true);
      treeViewer.getTree().setLayoutData(new GridData(GridData.FILL_BOTH));
      contentProvider = new ProjectInfoLazyTreeContentProvider();
      treeViewer.setContentProvider(contentProvider);
      labelProvider = new ProjectInfoLabelProvider(treeViewer);
      treeViewer.setLabelProvider(labelProvider);
      treeViewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
      ColumnViewerToolTipSupport.enableFor(treeViewer);
      MenuManager treeViewerMenuManager = new MenuManager();
      treeViewerMenuManager.setRemoveAllWhenShown(true);
      treeViewerMenuManager.addMenuListener(new IMenuListener() {
          @Override
         public void menuAboutToShow(IMenuManager manager) {
            handleTreeViewerMenuAboutToShow(manager);
         }
      });
      treeViewer.getTree().setMenu(treeViewerMenuManager.createContextMenu(treeViewer.getTree()));
      // legendComposite
      Composite legendComposite = new Composite(treeViewrLegendComposite, SWT.NONE);
      legendComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      GridLayout legendLayout = new GridLayout(6, false);
      legendLayout.marginBottom = 0;
      legendLayout.marginHeight = 0;
      legendLayout.marginLeft = 0;
      legendLayout.marginRight = 0;
      legendLayout.marginWidth = 0;
      legendLayout.verticalSpacing = 0;
      legendComposite.setLayout(legendLayout);
      Label legendLabel = new Label(legendComposite, SWT.NONE);
      legendLabel.setText("Colors: ");
      legendLabel.setToolTipText("Colors indicate the verification status and parents are colored according to the worst verification stati of their children.");
      cyclicProofsColor = new Color(legendLabel.getDisplay(), ProjectInfoColorTreeSynchronizer.COLOR_PROOF_IN_RECURSION_CYCLE);
      Label cylcicProofsLabel = new Label(legendComposite, SWT.NONE);
      cylcicProofsLabel.setForeground(cyclicProofsColor);
      cylcicProofsLabel.setText("Cyclic proofs");
      cylcicProofsLabel.setToolTipText("Proofs form a cylic specification use which invalidates all of them.");
      openProofColor = new Color(legendLabel.getDisplay(), ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
      Label openProofLabel = new Label(legendComposite, SWT.NONE);
      openProofLabel.setForeground(openProofColor);
      openProofLabel.setText("Open proof");
      openProofLabel.setToolTipText("A proof is still open which may indicate a bug or that KeY was not powerful enough to finish the proof automatially.");
      unspecifiedColor = new Color(legendLabel.getDisplay(), ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
      Label unspecifiedLabel = new Label(legendComposite, SWT.NONE);
      unspecifiedLabel.setForeground(unspecifiedColor);
      unspecifiedLabel.setText("Unspecified");
      unspecifiedLabel.setToolTipText("A method has no specification which is dangerous because it might call methods in illegal state which is not proven.");
      unprovenDependencyColor = new Color(legendLabel.getDisplay(), ProjectInfoColorTreeSynchronizer.COLOR_UNPROVEN_DEPENDENCY);
      Label unprovenDependencyLabel = new Label(legendComposite, SWT.NONE);
      unprovenDependencyLabel.setForeground(unprovenDependencyColor);
      unprovenDependencyLabel.setText("Unproven dependency");
      unprovenDependencyLabel.setToolTipText("A proof is sucefull closed but uses at least one unproven specification of the project.");
      closedProofColor = new Color(legendLabel.getDisplay(), ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF);
      Label closedProofLabel = new Label(legendComposite, SWT.NONE);
      closedProofLabel.setForeground(closedProofColor);
      closedProofLabel.setText("Closed proof");
      closedProofLabel.setToolTipText("A proof is sucefull closed and all used specifications of the project are proven as well.");
      updateShownContent();
      ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceChangeListener);
      KeYResourcesUtil.addKeYResourcePropertyListener(resourcePropertyListener);
      // reportBrowser
      reportBrowser = new Browser(tabFolder, SWT.BORDER);
      reportBrowser.addLocationListener(new LocationListener() {
         @Override
         public void changing(LocationEvent event) {
            handleReportBrowserChanging(event);
         }
         
         @Override
         public void changed(LocationEvent event) {
            handleReportBrowserChanged(event);
         }
      });
      reportBrowser.addStatusTextListener(new StatusTextListener() {
         @Override
         public void changed(StatusTextEvent event) {
            selectedReportBrowserText = event.text;
         }
      });
      MenuManager reportBrowserMenuManager = new MenuManager();
      reportBrowserMenuManager.setRemoveAllWhenShown(true);
      reportBrowserMenuManager.addMenuListener(new IMenuListener() {
         @Override
         public void menuAboutToShow(IMenuManager manager) {
            handleReportBrowserMenuAboutToShow(manager);
         }
      });
      reportBrowser.setMenu(reportBrowserMenuManager.createContextMenu(reportBrowser));
      // reportTabItem
      CTabItem reportTabItem = new CTabItem(tabFolder, SWT.NONE);
      reportTabItem.setText("&Report");
      reportTabItem.setControl(reportBrowser);
   }

   /**
    * Updates the shown content.
    */
   public void updateShownContent() {
      final Set<IResource> linkedResources = isLinkWithBasePart() ? computeLinkedResources() : null;      
      final Set<IProject> linkedProjects = listProjects(linkedResources);
      final List<IProject> newProjects = computeProjectsToShow(linkedProjects);
      if (!ObjectUtil.equals(projects, newProjects)) {
         projects = newProjects;
         if (colorSynchronizer != null) {
            colorSynchronizer.dispose();
         }
         removeProjectInfoListener();
         projectInfos = new HashMap<IProject, ProjectInfo>();
         for (IProject project : projects) {
            ProjectInfo info = ProjectInfoManager.getInstance().getProjectInfo(project);
            projectInfos.put(project, info);
            info.addProjectInfoListener(projectInfoListener);
         }
         labelProvider.setProjects(projects);
         treeViewer.setInput(projects);
         colorSynchronizer = new ProjectInfoColorTreeSynchronizer(projects, treeViewer);
      }
      rootComposite.getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            selectInTreeViewer(linkedResources);
         }
      });
      updateProgressBarsAndReport(); // Always update progress bars because method is called on any resource change
   }

   /**
    * Selects the given {@link IResource}s if possible.
    * @param linkedResources
    */
   protected void selectInTreeViewer(Set<IResource> resources) {
      if (resources != null) {
         Set<Object> toSelect = new HashSet<Object>();
         for (IResource resource : resources) {
            if (resource instanceof IProject) {
               toSelect.add(resource);
            }
            else if (resource != null) {
               ProjectInfo projectInfo = projectInfos.get(resource.getProject());
               if (projectInfo != null) {
                  Set<Object> modelElements = projectInfo.getModelElements(resource);
                  if (modelElements != null) {
                     for (Object element : modelElements) {
                        if (element instanceof PackageInfo || element instanceof TypeInfo) {
                           expandToInTreeViewer(element);
                           toSelect.add(element);
                        }
                     }
                  }
               }
            }
         }
         treeViewer.setSelection(SWTUtil.createSelection(toSelect.toArray()), true);
      }
   }
   
   /**
    * Expands the parents of the given element in {@link #treeViewer}.
    * @param element The element to expand its parents.
    */
   protected void expandToInTreeViewer(final Object element) {
      if (element != null) {
         Deque<Object> parents = new LinkedList<Object>();
         Object parent = ProjectInfoManager.getParent(element);
         while (parent != null) {
            parents.addFirst(parent);
            parent = ProjectInfoManager.getParent(parent);
         }
         for (Object toExpand : parents) {
            if (toExpand instanceof ProjectInfo) {
               toExpand = ((ProjectInfo) toExpand).getProject();
            }
            treeViewer.expandToLevel(toExpand, 1);
         }
      }
   }

   /**
    * Removes the listener from all {@link ProjectInfo}s in {@link #projectInfos}.
    */
   protected void removeProjectInfoListener() {
      if (projectInfos != null) {
         for (ProjectInfo info : projectInfos.values()) {
            info.removeProjectInfoListener(projectInfoListener);
         }
         projectInfos = null;
      }
   }
   
   /**
    * Computes the {@link IProject}s to show.
    * @param linkedProjects The optional {@link IProject}s linked with.
    * @return The {@link IProject}s to show.
    */
   protected List<IProject> computeProjectsToShow(Set<IProject> linkedProjects) {
      List<IProject> result = new LinkedList<IProject>();
      for (IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
         try {
            if (project.exists() && project.isOpen() && KeYResourcesUtil.isKeYProject(project)) {
               if (linkedProjects == null || linkedProjects.contains(project)) {
                  result.add(project);
               }
            }
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
      }
      return result;
   }

   /**
    * Handles a double click.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      selectInWorkbench(event.getSelection());
   }

   /**
    * Updates the context menu of {@link #treeViewer}.
    * @param manager The {@link IMenuManager} to update.
    */
   protected void handleTreeViewerMenuAboutToShow(IMenuManager manager) {
      Object[] elements = SWTUtil.toArray(treeViewer.getSelection());
      // Check if at least one proof file is available
      List<IFile> proofFiles = new LinkedList<IFile>();
      for (Object obj : elements) {
         if (obj instanceof ContractInfo) {
            IFile proofFile = ((ContractInfo) obj).getProofFile();
            if (proofFile != null && proofFile.exists()) {
               proofFiles.add(proofFile);
            }
         }
      }
      // Update menu
      if (!proofFiles.isEmpty()) {
         manager.add(createOpenProofsAction(proofFiles.toArray(new IFile[proofFiles.size()])));
      }
   }
   
   /**
    * Creates an {@link IAction} which allows to open given existing proof files.
    * @param proofFiles The existing proof files to open.
    * @return The created {@link IAction}.
    */
   protected IAction createOpenProofsAction(final IFile[] proofFiles) {
      IAction action = new Action("Open proof", KeYImages.getImageDescriptor(KeYImages.KEY_LOGO)) {
         @Override
         public void run() {
            openProofs(proofFiles);
         }
      };
      action.setEnabled(!ArrayUtil.isEmpty(proofFiles));
      return action;
   }
   
   /**
    * Creates an {@link IAction} which allows to open given existing proof files.
    * @param proofFiles The existing proof files to open.
    * @return The created {@link IAction}.
    */
   protected IAction createOpenFilesAction(final IFile[] files) {
      IAction action = new Action("Open file") {
         @Override
         public void run() {
            selectInWorkbench(SWTUtil.createSelection((Object[])files));
         }
      };
      if (!ArrayUtil.isEmpty(files)) {
         Image image = null;
         int i = 0;
         while (image == null && i < files.length) {
            image = WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getImage(files[i]);
            i++;
         }
         if (image != null) {
            action.setImageDescriptor(ImageDescriptor.createFromImage(image));
         }
         action.setEnabled(true);
      }
      else {
         action.setEnabled(false);
      }
      return action;
   }
   
   /**
    * Opens the selected proofs.
    * @param proofFiles The {@link IFile}s of the proofs to open.
    */
   protected void openProofs(IFile[] proofFiles) {
      try {
         for (IFile file : proofFiles) {
            StarterUtil.openFileStarter(rootComposite.getShell(), file);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(rootComposite.getShell(), e);
      }
   }

   /**
    * Selects the elements in the given {@link ISelection} in the {@link IWorkbench}.
    * @param selection The {@link ISelection} which provides the elements to select.
    */
   public void selectInWorkbench(ISelection selection) {
      Object[] elements = SWTUtil.toArray(selection);
      for (Object element : elements) {
         // Go back in parent hierarchy to find selectable element
         if (element instanceof ContractInfo) {
            ContractInfo info = (ContractInfo) element;
            element = info.getParent();
         }
         // Try to select element
         if (element instanceof IFile) {
            try {
               WorkbenchUtil.openEditor((IFile) element);
            }
            catch (PartInitException e) {
               LogUtil.getLogger().logError(e);
               LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
            }
         }
         else if (element instanceof IResource) {
            WorkbenchUtil.selectAndReveal((IResource)element);
         }
         else if (element instanceof PackageInfo) {
            PackageInfo info = (PackageInfo) element;
            IPackageFragment pf = info.findJDTPackage();
            if (pf != null && pf.exists()) {
               WorkbenchUtil.selectAndReveal(pf.getResource());
            }
         }
         else if (element instanceof TypeInfo) {
            try {
               TypeInfo info = (TypeInfo) element;
               if (info.getFile() != null) {
                  IEditorPart editor = WorkbenchUtil.openEditor(info.getFile());
                  if (editor instanceof JavaEditor) {
                     IType type = info.findJDTType();
                     if (type != null && type.exists()) {
                        ((JavaEditor) editor).setSelection(type);
                     }
                  }
               }
            }
            catch (PartInitException e) {
               LogUtil.getLogger().logError(e);
               LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
            }
         }
         else if (element instanceof MethodInfo) {
            try {
               MethodInfo info = (MethodInfo) element;
               if (info.getDeclaringFile() != null) {
                  IEditorPart editor = WorkbenchUtil.openEditor(info.getDeclaringFile());
                  if (editor instanceof JavaEditor) {
                     IMethod method = info.findJDTMethod();
                     if (method != null && method.exists()) {
                        ((JavaEditor) editor).setSelection(method);
                     }
                  }
               }
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e);
               LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
            }
         }
         else if (element instanceof ObserverFunctionInfo) {
            try {
               ObserverFunctionInfo info = (ObserverFunctionInfo) element;
               if (info.getDeclaringFile() != null) {
                  IEditorPart editor = WorkbenchUtil.openEditor(info.getDeclaringFile());
                  if (editor instanceof JavaEditor) {
                     IType type = info.findJDTDeclaringType();
                     if (type != null && type.exists()) {
                        ((JavaEditor) editor).setSelection(type);
                     }
                  }
               }
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e);
               LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
            }
         }
      }
   }
   
   /**
    * Updates the progress bars {@link #proofProgressBar} and {@link #specificationProgressBar}.
    */
   protected void updateProgressBarsAndReport() {
      if (activeJob != null) {
         activeJob.cancel();
      }
      activeJob = new Job("Computing verification status") {
         @Override
         protected IStatus run(IProgressMonitor monitor) {
            try {
               SWTUtil.checkCanceled(monitor);
               final VerificationStatus status = new VerificationStatus();
               if (projectInfos != null) {
                  for (ProjectInfo info : projectInfos.values()) {
                     SWTUtil.checkCanceled(monitor);
                     updateStatus(info, status, monitor);
                  }
               }
               SWTUtil.checkCanceled(monitor);
               if (!proofProgressBar.isDisposed()) {
                  proofProgressBar.getDisplay().syncExec(new Runnable() {
                     @Override
                     public void run() {
                        if (!proofProgressBar.isDisposed()) {
                           proofProgressBar.setToolTipText(status.numOfProvenContracts + " of " + status.numOfContracts + " proof obligations are proven" + (!status.cycles.isEmpty() ? ", but cyclic use of specifications detected" : "") + ".");
                           proofProgressBar.reset(status.numOfProvenContracts != status.numOfContracts, !status.cycles.isEmpty(), status.numOfProvenContracts, status.numOfContracts);
                           specificationProgressBar.setToolTipText(status.numOfSpecifiedMethods + " of " + status.numOfMethods + " methods are specified.");
                           specificationProgressBar.reset(status.numOfSpecifiedMethods != status.numOfMethods, false, status.numOfSpecifiedMethods, status.numOfMethods);
                        }
                     }
                  });
               }
               SWTUtil.checkCanceled(monitor);
               IRunnableWithResult<FontData> fontRun = new AbstractRunnableWithResult<FontData>() {
                  @Override
                  public void run() {
                     Font systemFont = Display.getDefault().getSystemFont();
                     setResult(systemFont.getFontData()[0]);
                  }
               };
               Display.getDefault().syncExec(fontRun);
               SWTUtil.checkCanceled(monitor);
               final String report = createHtmlReport(status, monitor, fontRun.getResult().getName(), fontRun.getResult().getHeight());
               SWTUtil.checkCanceled(monitor);
               if (!reportBrowser.isDisposed()) {
                  reportBrowser.getDisplay().syncExec(new Runnable() {
                     @Override
                     public void run() {
                        if (!reportBrowser.isDisposed() && !ObjectUtil.equals(report, reportBrowser.getData())) {
                           reportBrowser.setText(report, true);
                           reportBrowser.setData(report);
                        }
                     }
                  });
               }
               return Status.OK_STATUS;
            }
            catch (OperationCanceledException e) {
               return Status.CANCEL_STATUS;
            }
            catch (Exception e) {
               return LogUtil.getLogger().createErrorStatus(e);
            }
         }
         
         private String createHtmlReport(VerificationStatus status, IProgressMonitor monitor, String font, int fontSize) throws Exception {
            StringBuffer sb = new StringBuffer();
            // Add header
            sb.append("<html>" + StringUtil.NEW_LINE);
            sb.append("<header>" + StringUtil.NEW_LINE);
            sb.append("<title>Report</title>" + StringUtil.NEW_LINE);
            sb.append("<style type=\"text/css\">" + StringUtil.NEW_LINE);
            sb.append("html {font-family:'" + font + "'; font-size:" + fontSize + "pt;}" + StringUtil.NEW_LINE);
            sb.append("h1 {font-family:'" + font + "'; font-size:" + (fontSize + 2) + "pt; margin-top: " + ((fontSize + 2) / 2) + "pt; margin-bottom: 1pt;}" + StringUtil.NEW_LINE);
            sb.append("ol {margin-top: 0pt; margin-bottom: 0pt;}" + StringUtil.NEW_LINE);
            sb.append("ul {margin-top: 0pt; margin-bottom: 0pt;}" + StringUtil.NEW_LINE);
            sb.append("li {margin-top: 1pt; margin-bottom: 1pt;}" + StringUtil.NEW_LINE);
            sb.append("a:link { color:blue; text-decoration:none; }" + StringUtil.NEW_LINE);
            sb.append("a:visited { color:blue; text-decoration:none; }" + StringUtil.NEW_LINE);
            sb.append("a:focus { color:blue; text-decoration:none; }" + StringUtil.NEW_LINE);
            sb.append("a:hover { color:blue; text-decoration:underline; }" + StringUtil.NEW_LINE);
            sb.append("a:active { color:blue; text-decoration:none; }" + StringUtil.NEW_LINE);
            sb.append("</style>" + StringUtil.NEW_LINE);
            sb.append("</header>" + StringUtil.NEW_LINE);
            sb.append("<body>" + StringUtil.NEW_LINE);
            sb.append("<h1><a name=\"Contents\">List of Contents</a></h1>" + StringUtil.NEW_LINE);
            sb.append("<ol>" + StringUtil.NEW_LINE);
            if (!status.cycles.isEmpty()) {
               sb.append("<li><a href=\"#CyclicProofs\">Cyclic Specification use in Proofs</a></li>" + StringUtil.NEW_LINE);
            }
            if (!status.unprovenContracts.isEmpty()) {
               sb.append("<li><a href=\"#OpenProofs\">Open Proofs</a></li>" + StringUtil.NEW_LINE);
            }
            if (!status.unspecifiedMethods.isEmpty()) {
               sb.append("<li><a href=\"#UnspecifiedMethods\">Unspecified Methods</a></li>" + StringUtil.NEW_LINE);
            }
            if (!status.unsoundTacletOptions.isEmpty()) {
               sb.append("<li><a href=\"#TacletOptionsUnsound\">" + ChoiceEntry.UNSOUND_TEXT + " Taclet Options</a></li>" + StringUtil.NEW_LINE);
            }
            if (!status.incomplelteTacletOptions.isEmpty()) {
               sb.append("<li><a href=\"#TacletOptionsIncomplete\">" + ChoiceEntry.INCOMPLETE_TEXT  + " Taclet Options</a></li>" + StringUtil.NEW_LINE);
            }
            if (!status.informationTacletOptions.isEmpty()) {
               sb.append("<li><a href=\"#TacletOptionsInformation\">Taclet Options with additional Information</a></li>" + StringUtil.NEW_LINE);
            }
            sb.append("<li><a href=\"#Assumptions\">Assumptions</a></li>" + StringUtil.NEW_LINE);
            sb.append("</ol>" + StringUtil.NEW_LINE);
            // Add cyclic proofs
            if (!status.cycles.isEmpty()) {
               sb.append("<h1><a name=\"CyclicProofs\">Cyclic Specification use in Proofs</a></h1>" + StringUtil.NEW_LINE);
               sb.append("<ol>" + StringUtil.NEW_LINE);
               for (List<IFile> cycle : status.cycles) {
                  SWTUtil.checkCanceled(monitor);
                  sb.append("<li>The following proofs forms a cyclic specification use which invalidates all of them:" + StringUtil.NEW_LINE);
                  sb.append("<ul>" + StringUtil.NEW_LINE);
                  for (IFile file : cycle) {
                     SWTUtil.checkCanceled(monitor);
                     sb.append("<li>Participating proof: <a href=\"" + toURL(file) + "\">" + StringUtil.NEW_LINE);
                     sb.append(file.getFullPath());
                     sb.append("</a></li>" + StringUtil.NEW_LINE);
                  }
                  sb.append("</ul>" + StringUtil.NEW_LINE);
                  sb.append("</li>" + StringUtil.NEW_LINE);
               }
               sb.append("</ol>" + StringUtil.NEW_LINE);
            }
            // Add open proofs
            if (!status.unprovenContracts.isEmpty()) {
               sb.append("<h1><a name=\"OpenProofs\">Open Proofs</a></h1>" + StringUtil.NEW_LINE);
               sb.append((status.numOfContracts - status.numOfProvenContracts) + " of " + status.numOfContracts + " proof" + ((status.numOfContracts - status.numOfProvenContracts) == 1 ? " is" : "s are") + " still open: " + StringUtil.NEW_LINE);
               sb.append("<ol>" + StringUtil.NEW_LINE);
               for (ContractInfo contractInfo : status.unprovenContracts) {
                  SWTUtil.checkCanceled(monitor);
                  sb.append("<li>" + StringUtil.NEW_LINE);
                  sb.append("<a href=\"" + toURL(contractInfo.getProofFile()) + "\">");
                  sb.append(contractInfo.getProofFile().getFullPath());
                  sb.append("</a>" + StringUtil.NEW_LINE);
                  List<IFile> usedByFiles = status.usedByProofs.get(contractInfo.getProofFile());
                  if (!CollectionUtil.isEmpty(usedByFiles)) {
                     sb.append("<ul>" + StringUtil.NEW_LINE);
                     for (IFile usedByFile : usedByFiles) {
                        SWTUtil.checkCanceled(monitor);
                        sb.append("<li>Used by proof: <a href=\"" + toURL(usedByFile) + "\">" + StringUtil.NEW_LINE);
                        sb.append(usedByFile.getFullPath());
                        sb.append("</a></li>" + StringUtil.NEW_LINE);
                     }
                     sb.append("</ul>" + StringUtil.NEW_LINE);
                  }
                  sb.append("</li>" + StringUtil.NEW_LINE);
               }
               sb.append("</ol>" + StringUtil.NEW_LINE);
            }
            // Add unspecified methods
            if (!status.unspecifiedMethods.isEmpty()) {
               sb.append("<h1><a name=\"UnspecifiedMethods\">Unspecified Methods</a></h1>" + StringUtil.NEW_LINE);
               sb.append((status.numOfMethods - status.numOfSpecifiedMethods) + " of " + status.numOfMethods + " method" + ((status.numOfMethods - status.numOfSpecifiedMethods) == 1 ? " is" : "s are") + " unspecified and may call methods in a state not satisfying the precondition: " + StringUtil.NEW_LINE);
               sb.append("<ol>" + StringUtil.NEW_LINE);
               for (Entry<TypeInfo, List<MethodInfo>> entry : status.unspecifiedMethods.entrySet()) {
                  SWTUtil.checkCanceled(monitor);
                  sb.append("<li>" + StringUtil.NEW_LINE);
                  sb.append("<a href=\"" + toURL(entry.getKey().getFile()) + "\">");
                  sb.append(computeFullQualifiedName(entry.getKey()));
                  sb.append("</a>" + StringUtil.NEW_LINE);
                  sb.append("<ul>" + StringUtil.NEW_LINE);
                  for (MethodInfo method : entry.getValue()) {
                     SWTUtil.checkCanceled(monitor);
                     sb.append("<li>" + method.getDisplayName() + "</li>" + StringUtil.NEW_LINE);
                  }
                  sb.append("</ul>" + StringUtil.NEW_LINE);
                  sb.append("</li>" + StringUtil.NEW_LINE);
               }
               sb.append("</ol>" + StringUtil.NEW_LINE);
            }
            // Add unsound taclet options
            if (!status.unsoundTacletOptions.isEmpty()) {
               sb.append("<h1><a name=\"TacletOptionsUnsound\">" + ChoiceEntry.UNSOUND_TEXT + " Taclet Options</a></h1>" + StringUtil.NEW_LINE);
               sb.append("Proofs using a listed taclet options are " + ChoiceEntry.UNSOUND_TEXT + ":" + StringUtil.NEW_LINE);
               sb.append("<ol>" + StringUtil.NEW_LINE);
               SWTUtil.checkCanceled(monitor);
               for (Entry<String, List<IFile>> entry : status.unsoundTacletOptions.entrySet()) {
                  sb.append("<li>" + StringUtil.NEW_LINE);
                  sb.append(ChoiceSelector.createChoiceEntry(entry.getKey()) + StringUtil.NEW_LINE);
                  sb.append("<ul>" + StringUtil.NEW_LINE);
                  for (IFile usedByFile : entry.getValue()) {
                     SWTUtil.checkCanceled(monitor);
                     sb.append("<li>Used by proof: <a href=\"" + toURL(usedByFile) + "\">" + StringUtil.NEW_LINE);
                     sb.append(usedByFile.getFullPath());
                     sb.append("</a></li>" + StringUtil.NEW_LINE);
                  }
                  sb.append("</ul>" + StringUtil.NEW_LINE);
                  sb.append("</li>" + StringUtil.NEW_LINE);
               }
               sb.append("</ol>" + StringUtil.NEW_LINE);
            }
            // Add incomplete taclet options
            if (!status.incomplelteTacletOptions.isEmpty()) {
               sb.append("<h1><a name=\"TacletOptionsIncomplete\">" + ChoiceEntry.INCOMPLETE_TEXT + " Taclet Options</a></h1>" + StringUtil.NEW_LINE);
               sb.append("Proofs using a listed taclet options are " + ChoiceEntry.INCOMPLETE_TEXT + ":" + StringUtil.NEW_LINE);
               sb.append("<ol>" + StringUtil.NEW_LINE);
               for (Entry<String, List<IFile>> entry : status.incomplelteTacletOptions.entrySet()) {
                  SWTUtil.checkCanceled(monitor);
                  sb.append("<li>" + StringUtil.NEW_LINE);
                  sb.append(ChoiceSelector.createChoiceEntry(entry.getKey()) + StringUtil.NEW_LINE);
                  sb.append("<ul>" + StringUtil.NEW_LINE);
                  for (IFile usedByFile : entry.getValue()) {
                     SWTUtil.checkCanceled(monitor);
                     sb.append("<li>Used by proof: <a href=\"" + toURL(usedByFile) + "\">" + StringUtil.NEW_LINE);
                     sb.append(usedByFile.getFullPath());
                     sb.append("</a></li>" + StringUtil.NEW_LINE);
                  }
                  sb.append("</ul>" + StringUtil.NEW_LINE);
                  sb.append("</li>" + StringUtil.NEW_LINE);
               }
               sb.append("</ol>" + StringUtil.NEW_LINE);
            }
            // Add information taclet options
            if (!status.informationTacletOptions.isEmpty()) {
               sb.append("<h1><a name=\"TacletOptionsInformation\">Taclet Options with additional Information</a></h1>" + StringUtil.NEW_LINE);
               sb.append("Proofs using a taclet option with some additional information:" + StringUtil.NEW_LINE);
               sb.append("<ol>" + StringUtil.NEW_LINE);
               for (Entry<String, List<IFile>> entry : status.informationTacletOptions.entrySet()) {
                  SWTUtil.checkCanceled(monitor);
                  sb.append("<li>" + StringUtil.NEW_LINE);
                  sb.append(ChoiceSelector.createChoiceEntry(entry.getKey()) + StringUtil.NEW_LINE);
                  sb.append("<ul>" + StringUtil.NEW_LINE);
                  for (IFile usedByFile : entry.getValue()) {
                     SWTUtil.checkCanceled(monitor);
                     sb.append("<li>Used by proof: <a href=\"" + toURL(usedByFile) + "\">" + StringUtil.NEW_LINE);
                     sb.append(usedByFile.getFullPath());
                     sb.append("</a></li>" + StringUtil.NEW_LINE);
                  }
                  sb.append("</ul>" + StringUtil.NEW_LINE);
                  sb.append("</li>" + StringUtil.NEW_LINE);
               }
               sb.append("</ol>" + StringUtil.NEW_LINE);
            }
            // Add assumptions
            sb.append("<h1><a name=\"Assumptions\">Assumptions</a></h1>" + StringUtil.NEW_LINE);
            sb.append("Proofs are performed under the following assumptions still need to be proven:" + StringUtil.NEW_LINE);
            sb.append("<ol>" + StringUtil.NEW_LINE);
            for (Entry<ProofMetaFileAssumption, List<IFile>> entry : status.assumptions.entrySet()) {
               SWTUtil.checkCanceled(monitor);
               sb.append("<li>" + StringUtil.NEW_LINE);
               sb.append(entry.getKey() + StringUtil.NEW_LINE);
               sb.append("<ul>" + StringUtil.NEW_LINE);
               for (IFile file : entry.getValue()) {
                  SWTUtil.checkCanceled(monitor);
                  sb.append("<li>Used by proof: <a href=\"" + toURL(file) + "\">" + StringUtil.NEW_LINE);
                  sb.append(file.getFullPath());
                  sb.append("</a></li>" + StringUtil.NEW_LINE);
               }
               sb.append("</ul>" + StringUtil.NEW_LINE);
               sb.append("</li>" + StringUtil.NEW_LINE);
            }
            sb.append("<li>Methods are called in a state satisfying the precondition, assumed for:" + StringUtil.NEW_LINE);
            sb.append("<ol>" + StringUtil.NEW_LINE);
            if (!status.unspecifiedMethods.isEmpty()) {
               sb.append("<li><a href=\"#UnspecifiedMethods\">Unspecified methods</a></li>" + StringUtil.NEW_LINE);
            }
            sb.append("<li>Methods of used APIs</li>" + StringUtil.NEW_LINE);
            sb.append("<li>Projects in which the source code will be used</li>" + StringUtil.NEW_LINE);
            sb.append("</ol>" + StringUtil.NEW_LINE);
            sb.append("</li>" + StringUtil.NEW_LINE);
            sb.append("<li><i>Source code is compiled using a correct Java compiler.</i></li>" + StringUtil.NEW_LINE);
            sb.append("<li><i>Program is run on a a correct JVM.</i></li>" + StringUtil.NEW_LINE);
            sb.append("</ol>" + StringUtil.NEW_LINE);
            // Add footer
            sb.append("</body>" + StringUtil.NEW_LINE);
            sb.append("</html>");
            return sb.toString();
         }

         private String toURL(IFile file) {
            if (file != null) {
               File localFile = ResourceUtil.getLocation(file);
               return localFile != null ? 
                      PROTOCOL_FILE_PREFIX + localFile.getAbsolutePath().replace(File.separatorChar, '/') : 
                      PROTOCOL_RESOURCE + file.getFullPath();
            }
            else {
               return null;
            }
         }
         
         private void updateStatus(ProjectInfo projectInfo, VerificationStatus status, IProgressMonitor monitor) throws Exception {
            for (PackageInfo packageInfo : projectInfo.getPackages()) {
               SWTUtil.checkCanceled(monitor);
               updateStatus(packageInfo, status, monitor);
            }
         }

         private void updateStatus(PackageInfo packageInfo, VerificationStatus status, IProgressMonitor monitor) throws Exception {
            for (TypeInfo typeInfo : packageInfo.getTypes()) {
               SWTUtil.checkCanceled(monitor);
               updateStatus(typeInfo, status, monitor);
            }
         }

         private void updateStatus(TypeInfo typeInfo, VerificationStatus status, IProgressMonitor monitor) throws Exception {
            for (MethodInfo methodInfo : typeInfo.getMethods()) {
               SWTUtil.checkCanceled(monitor);
               status.numOfMethods++;
               if (methodInfo.countContracts() >= 1) {
                  status.numOfSpecifiedMethods++;
                  for (ContractInfo contractInfo : methodInfo.getContracts()) {
                     SWTUtil.checkCanceled(monitor);
                     updateStatus(contractInfo, status);
                  }
               }
               else {
                  List<MethodInfo> list = status.unspecifiedMethods.get(typeInfo);
                  if (list == null) {
                     list = new LinkedList<MethodInfo>();
                     status.unspecifiedMethods.put(typeInfo, list);
                  }
                  list.add(methodInfo);
               }
            }
            for (ObserverFunctionInfo observerFunctionInfo : typeInfo.getObserverFunctions()) {
               SWTUtil.checkCanceled(monitor);
               for (ContractInfo contractInfo : observerFunctionInfo.getContracts()) {
                  SWTUtil.checkCanceled(monitor);
                  updateStatus(contractInfo, status);
               }
            }
            for (TypeInfo internalTypeInfo : typeInfo.getTypes()) {
               SWTUtil.checkCanceled(monitor);
               updateStatus(internalTypeInfo, status, monitor);
            }
         }

         private void updateStatus(ContractInfo contractInfo, VerificationStatus status) throws Exception {
            status.numOfContracts++;
            // Closed state
            Boolean closed;
            try {
               closed = contractInfo.checkProofClosed();
            }
            catch (CoreException e) {
               LogUtil.getLogger().logError(e);
               closed = null;
            }
            if (closed != null && closed.booleanValue()) {
               status.numOfProvenContracts++;
            }
            else {
               status.unprovenContracts.add(contractInfo);
            }
            // Unproven dependencies
            List<IFile> unprovenDependencies = contractInfo.checkUnprovenDependencies();
            if (unprovenDependencies != null) {
               for (IFile file : unprovenDependencies) {
                  List<IFile> list = status.usedByProofs.get(file);
                  if (list == null) {
                     list = new LinkedList<IFile>();
                     status.usedByProofs.put(file, list);
                  }
                  list.add(contractInfo.getProofFile());
               }
            }
            // Assumptions
            List<ProofMetaFileAssumption> assumptions = contractInfo.checkAssumptions();
            if (assumptions != null) {
               for (ProofMetaFileAssumption assumption : assumptions) {
                  List<IFile> files = status.assumptions.get(assumption);
                  if (files == null) {
                     files = new LinkedList<IFile>();
                     status.assumptions.put(assumption, files);
                  }
                  files.add(contractInfo.getProofFile());
               }
            }
            // Taclet options
            TacletOptionIssues issues = contractInfo.checkTaletOptions();
            if (issues != null) {
               for (String choice : issues.getUnsoundOptions()) {
                  List<IFile> list = status.unsoundTacletOptions.get(choice);
                  if (list == null) {
                     list = new LinkedList<IFile>();
                     status.unsoundTacletOptions.put(choice, list);
                  }
                  list.add(contractInfo.getProofFile());
               }
               for (String choice : issues.getIncompleteOptions()) {
                  List<IFile> list = status.incomplelteTacletOptions.get(choice);
                  if (list == null) {
                     list = new LinkedList<IFile>();
                     status.incomplelteTacletOptions.put(choice, list);
                  }
                  list.add(contractInfo.getProofFile());
               }
               for (String choice : issues.getInformationOptions()) {
                  List<IFile> list = status.informationTacletOptions.get(choice);
                  if (list == null) {
                     list = new LinkedList<IFile>();
                     status.informationTacletOptions.put(choice, list);
                  }
                  list.add(contractInfo.getProofFile());
               }
            }
            // Cycles
            List<IFile> cycle = contractInfo.checkProofRecursionCycle();
            if (!CollectionUtil.isEmpty(cycle)) {
               status.cycles.add(cycle);
            }
         }
      };
      activeJob.setRule(ResourcesPlugin.getWorkspace().getRuleFactory().buildRule());
      activeJob.schedule();
   }

   /**
    * Computes the full qualified type name.
    * @param type The {@link TypeInfo}.
    * @return The full qualified name of the given {@link TypeInfo}.
    */
   protected String computeFullQualifiedName(TypeInfo type) {
      StringBuffer sb = new StringBuffer();
      sb.append(type.getName());
      Object parent = ProjectInfoManager.getParent(type);
      while (parent != null) {
         if (parent instanceof TypeInfo) {
            sb.insert(0, '.');
            sb.insert(0, ((TypeInfo) parent).getName());
            parent = ProjectInfoManager.getParent(parent);
         }
         else if (parent instanceof PackageInfo) {
            String name = ((PackageInfo) parent).getName();
            if (!PackageInfo.DEFAULT_NAME.equals(name)) {
               sb.insert(0, '.');
               sb.insert(0, name);
            }
            parent = null;
         }
         else {
            // Should never be executed, only to ensure endless loops
            parent = ProjectInfoManager.getParent(parent);
         }
      }
      return sb.toString();
   }

   /**
    * When the content in {@link #reportBrowser} should be changed.
    * @param event The event.
    */
   @SuppressWarnings("deprecation")
   protected void handleReportBrowserChanging(LocationEvent event) {
      if (event.location != null) {
         event.doit = event.location.startsWith("about:blank");
         if (!event.location.startsWith("about:blank#")) {
            IFile[] files = null;
            if (event.location.startsWith(PROTOCOL_RESOURCE)) {
               String location = event.location.substring(PROTOCOL_RESOURCE.length());
               IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(location));
               if (file.exists()) {
                  files = new IFile[] {file};
               }
            }
            else if (event.location.startsWith(PROTOCOL_FILE_PREFIX)) {
               String location = event.location.substring(PROTOCOL_FILE_PREFIX.length());
               files = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocation(new Path(location));
            }
            if (!ArrayUtil.isEmpty(files)) {
               if (event.location.endsWith(KeYUtil.PROOF_FILE_EXTENSION) ||
                   event.location.endsWith(KeYUtil.KEY_FILE_EXTENSION)) {
                  openProofs(files);
               }
               else {
                  selectInWorkbench(SWTUtil.createSelection((Object[])files));
               }
            }
         }
      }
   }

   /**
    * When the content in {@link #reportBrowser} has changed.
    * @param event The event.
    */
   protected void handleReportBrowserChanged(LocationEvent event) {
   }

   /**
    * Creates the context menu to show in {@link #reportBrowser}.
    * @param manager The {@link IMenuManager} to update.
    */
   @SuppressWarnings("deprecation")
   protected void handleReportBrowserMenuAboutToShow(IMenuManager manager) {
      if (selectedReportBrowserText != null) {
         IFile[] files = null;
         if (selectedReportBrowserText.startsWith(PROTOCOL_RESOURCE)) {
            String location = selectedReportBrowserText.substring(PROTOCOL_RESOURCE.length());
            IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(location));
            if (file.exists()) {
               files = new IFile[] {file};
            }
         }
         else if (selectedReportBrowserText.startsWith(PROTOCOL_FILE_PREFIX)) {
            String location = selectedReportBrowserText.substring(PROTOCOL_FILE_PREFIX.length());
            files = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocation(new Path(location));
         }
         if (!ArrayUtil.isEmpty(files)) {
            if (selectedReportBrowserText.endsWith(KeYUtil.PROOF_FILE_EXTENSION) ||
                selectedReportBrowserText.endsWith(KeYUtil.KEY_FILE_EXTENSION)) {
               manager.add(createOpenProofsAction(files));
            }
            else {
               manager.add(createOpenFilesAction(files));
            }
         }
      }
      manager.add(new Separator());
      manager.add(createCopyHTMLAction());
   }
   
   /**
    * Creates the action which copies the HTML report into the {@link Clipboard}.
    * @return The created action.
    */
   protected IAction createCopyHTMLAction() {
      IAction action = new Action("Copy HTML", PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_TOOL_COPY)) {
         @Override
         public void run() {
            copyReportToClipboard();
         }
      };
      action.setEnabled(reportBrowser.getData() instanceof String);
      return action;
   }
   
   /**
    * Copies the HTML report into the {@link Clipboard}.
    */
   protected void copyReportToClipboard() {
      if (reportBrowser.getData() instanceof String) {
         Clipboard clipboard = new Clipboard(reportBrowser.getDisplay());
         String htmlText = (String) reportBrowser.getData();
         TextTransfer textTransfer = TextTransfer.getInstance();
         HTMLTransfer htmlTransfer = HTMLTransfer.getInstance();
         clipboard.setContents(new String[]{htmlText, htmlText}, new Transfer[]{textTransfer, htmlTransfer});
         clipboard.dispose();
      }
   }

   /**
    * Utility class used by {@link VerificationStatus#updateProgressBarsAndReport()}
    * @author Martin Hentschel
    */
   private static class VerificationStatus {
      /**
       * The number of contracts.
       */
      private int numOfContracts = 0;
      
      /**
       * The number of proven contracts.
       */
      private int numOfProvenContracts = 0;
      
      /**
       * The number of methods.
       */
      private int numOfMethods = 0;
      
      /**
       * The number of specified methods.
       */
      private int numOfSpecifiedMethods = 0;
      
      /**
       * All unproven contracts.
       */
      private final List<ContractInfo> unprovenContracts = new LinkedList<ContractInfo>();
      
      /**
       * Maps a proof file to all proof files in which it is used.
       */
      private final Map<IFile, List<IFile>> usedByProofs = new HashMap<IFile, List<IFile>>();

      /**
       * Maps a used unsound taclet option to the proofs in which it is used.
       */
      private final Map<String, List<IFile>> unsoundTacletOptions = new LinkedHashMap<String, List<IFile>>();

      /**
       * Maps a used incomplete taclet option to the proofs in which it is used.
       */
      private final Map<String, List<IFile>> incomplelteTacletOptions = new LinkedHashMap<String, List<IFile>>();

      /**
       * Maps a used taclet option with an information to the proofs in which it is used.
       */
      private final Map<String, List<IFile>> informationTacletOptions = new LinkedHashMap<String, List<IFile>>();
      
      /**
       * Lists all unspecified {@link MethodInfo}s of a {@link TypeInfo}.
       */
      private final Map<TypeInfo, List<MethodInfo>> unspecifiedMethods = new LinkedHashMap<TypeInfo, List<MethodInfo>>();
      
      /**
       * The made assumptions.
       */
      private final Map<ProofMetaFileAssumption, List<IFile>> assumptions = new LinkedHashMap<ProofMetaFileAssumption, List<IFile>>();
      
      /**
       * All recursion cycles.
       */
      private final Set<List<IFile>> cycles = new LinkedHashSet<List<IFile>>();
   }
   
   /**
    * When a new {@link TypeInfo} was added to the given {@link AbstractTypeContainer}.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param type The added {@link TypeInfo}.
    * @param index The index.
    */
   protected void handleTypeAdded(final AbstractTypeContainer tcInfo, final TypeInfo type, final int index) {
      updateProgressBarsAndReport();
   }

   /**
    * When existing {@link TypeInfo}s were removed.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param types The removed {@link TypeInfo}s.
    */
   protected void handleTypesRemoved(final AbstractTypeContainer tcInfo, final Collection<TypeInfo> types) {
      updateProgressBarsAndReport();
   }
   
   /**
    * When a new {@link MethodInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param method The added {@link MethodInfo}.
    * @param index The index.
    */
   protected void handleMethodAdded(final TypeInfo type, final MethodInfo method, final int index) {
      updateProgressBarsAndReport();
   }

   /**
    * When existing {@link MethodInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param methods The removed {@link MethodInfo}s.
    */
   protected void handleMethodsRemoved(final TypeInfo type, final Collection<MethodInfo> methods) {
      updateProgressBarsAndReport();
   }

   /**
    * When a new {@link ObserverFunctionInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunction The added {@link ObserverFunctionInfo}.
    * @param index The index.
    */
   protected void handleObserverFunctionAdded(final TypeInfo type, final ObserverFunctionInfo observerFunction, final int index) {
      updateProgressBarsAndReport();
   }

   /**
    * When existing {@link ObserverFunctionInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunctions The removed {@link ObserverFunctionInfo}s.
    */
   protected void handleObserFunctionsRemoved(final TypeInfo type, final Collection<ObserverFunctionInfo> observerFunctions) {
      updateProgressBarsAndReport();
   }

   /**
    * When a new {@link ContractInfo} was added to the given {@link AbstractContractContainer}.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contract The added {@link ContractInfo}.
    * @param index The index.
    */
   protected void handleContractAdded(final AbstractContractContainer cc, final ContractInfo contract, final int index) {
      updateProgressBarsAndReport();
   }

   /**
    * When existing {@link ContractInfo}s were removed.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contracts The removed {@link ContractInfo}s.
    */
   protected void handleContractsRemoved(final AbstractContractContainer cc, final Collection<ContractInfo> contracts) {
      updateProgressBarsAndReport();
   }

   /**
    * When a new {@link PackageInfo} was added to the given {@link ProjectInfo}.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packageInfo The added {@link PackageInfo}.
    * @param index The index.
    */
   protected void handlePackageAdded(final ProjectInfo projectInfo, final PackageInfo packageInfo, final int index) {
      updateProgressBarsAndReport();
   }

   /**
    * When existing {@link PackageInfo}s were removed.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packages The removed {@link PackageInfo}s.
    */
   protected void handlePackagesRemoved(final ProjectInfo projectInfo, final Collection<PackageInfo> packages) {
      updateProgressBarsAndReport();
   }

   /**
    * When some {@link IResource}s have changed.
    * @param event The {@link IResourceChangeEvent}.
    */
   protected void handleResourceChanged(IResourceChangeEvent event) {
      updateShownContentThreadSave();
   }

   /**
    * The proof closed persistent property has changed via
    * {@link KeYResourcesUtil#setProofClosed(IFile, Boolean)}.
    * @param proofFile The changed proof file.
    * @param closed The new closed state.
    */
   protected void handleProofClosedChanged(IFile proofFile, Boolean closed) {
      updateShownContentThreadSave();
   }

   /**
    * The proof recursion cycle persistent property has changed via
    * {@link KeYResourcesUtil#setProofRecursionCycle(IFile, List)}.
    * @param proofFile The changed proof file.
    * @param cycle The new recursion cycle or {@code null} if not part of a cycle.
    */
   protected void handlProofRecursionCycleChanged(IFile proofFile, List<IFile> cycle) {
      updateShownContentThreadSave();
   }

   /**
    * Calls {@link #updateShownContent()} thread save.
    */
   protected void updateShownContentThreadSave() {
      if (!treeViewer.getTree().isDisposed()) {
         treeViewer.getTree().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               updateShownContent();
            }
         });
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      rootComposite.setFocus();
   }

   /**
    * When a property on {@link #basePart} has changed.
    * @param source The source {@link Object}.
    * @param propId The ID of the changed property.
    */
   protected void handleBasePartPropertyChanged(Object source, int propId) {
      if (propId == EditorPart.PROP_INPUT) {
         updateShownContent();
      }
   }

   /**
    * When the selection on {@link #basePart} has changed.
    * @param event The {@link SelectionChangedEvent}.
    */
   protected void handleBasePartSelectionChanged(SelectionChangedEvent event) {
      if (event.getSelection() instanceof IStructuredSelection) {
         updateShownContent();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePartActivated(IWorkbenchPart part) {
      updateBasePart();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePartDeactivated(IWorkbenchPart part) {
      updateBasePart();
   }
   
   /**
    * Updates {@link #basePart} and if required the shown content.
    */
   protected void updateBasePart() {
      IWorkbenchPart activePart = getSite().getPage().getActivePart();
      if (activePart != this) {
         if (activePart != basePart) {
            if (basePart instanceof EditorPart) {
               ((EditorPart) basePart).removePropertyListener(basePartListener);
            }
            if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
               basePart.getSite().getSelectionProvider().removeSelectionChangedListener(basePartSelectionChangedListener);
            }
            basePart = activePart;
            if (basePart instanceof EditorPart) {
               ((EditorPart) basePart).addPropertyListener(basePartListener);
            }
            if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
               basePart.getSite().getSelectionProvider().addSelectionChangedListener(basePartSelectionChangedListener);
            }
            if (isLinkWithBasePart()) {
               updateShownContent();
            }
         }
      }
   }

   /**
    * Checks if the shown content is linked with the selected {@link IWorkbenchPart}.
    * @return {@code true} is linked, {@code false} is independent.
    */
   public boolean isLinkWithBasePart() {
      boolean linkWith = false;
      if (linkState != null) {
         Object value = linkState.getValue();
         linkWith = value instanceof Boolean && ((Boolean) value).booleanValue();
      }
      return linkWith;
   }
   
   /**
    * Computes the {@link IResource} linked with.
    * @return The {@link IResource}s linked with.
    */
   protected Set<IResource> computeLinkedResources() {
      Set<IResource> result = new HashSet<IResource>();
      if (basePart instanceof IEditorPart) {
         IEditorInput input = ((IEditorPart) basePart).getEditorInput();
         if (input instanceof IFileEditorInput) {
            IFile file = ((IFileEditorInput) input).getFile();
            if (file != null) {
               result.add(file);
            }
         }
      }
      if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
         ISelection selection = basePart.getSite().getSelectionProvider().getSelection();
         Object[] elements = SWTUtil.toArray(selection);
         for (Object element : elements) {
            if (element instanceof IResource) {
               result.add((IResource) element);
            }
            else if (element instanceof IAdaptable) {
               Object adapted = ((IAdaptable) element).getAdapter(IResource.class);
               if (adapted instanceof IResource) {
                  result.add((IResource) adapted);
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Lists all {@link IProject}s of the given {@link IResource}s.
    * @param resources The {@link IResource}s to list its {@link IProject}s.
    * @return The {@link IProject}s or {@code null} if no {@link IResource}s where given..
    */
   protected Set<IProject> listProjects(Set<IResource> resources) {
      if (!CollectionUtil.isEmpty(resources)) {
         Set<IProject> projects = new HashSet<IProject>();
         for (IResource resource : resources) {
            projects.add(resource.getProject());
         }
         return projects;
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (activeJob != null) {
         activeJob.cancel();
      }
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceChangeListener);
      KeYResourcesUtil.removeKeYResourcePropertyListener(resourcePropertyListener);
      removeProjectInfoListener();
      if (basePart instanceof EditorPart) {
         ((EditorPart) basePart).removePropertyListener(basePartListener);
      }
      if (basePart != null && basePart.getSite() != null && basePart.getSite().getSelectionProvider() != null) {
         basePart.getSite().getSelectionProvider().removeSelectionChangedListener(basePartSelectionChangedListener);
      }
      if (linkState != null) {
         linkState.removeListener(stateListener);
      }
      if (colorSynchronizer != null) {
         colorSynchronizer.dispose();
      }
      if (contentProvider != null) {
         contentProvider.dispose();
      }
      if (labelProvider != null) {
         labelProvider.dispose();
      }
      if (openProofColor != null) {
         openProofColor.dispose();
      }
      if (closedProofColor != null) {
         closedProofColor.dispose();
      }
      if (unspecifiedColor != null) {
         unspecifiedColor.dispose();
      }
      if (unprovenDependencyColor != null) {
         unprovenDependencyColor.dispose();
      }
      if (cyclicProofsColor != null) {
         cyclicProofsColor.dispose();
      }
      super.dispose();
   }
}
