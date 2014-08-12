package org.key_project.key4eclipse.resources.ui.view;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;
import org.key_project.key4eclipse.resources.io.ProofMetaFileAssumption;
import org.key_project.key4eclipse.resources.projectinfo.AbstractContractContainer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractTypeContainer;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
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
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.job.AbstractDependingOnObjectsJob;
import org.key_project.util.eclipse.swt.CustomProgressBar;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.ObservableTreeViewer;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * This {@link IViewPart} shows the verification status.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class VerificationStatusView extends ViewPart {
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
   private List<ProjectInfo> projectInfos;
   
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
    * The text which shows assumptions
    */
   private Text assumptionText;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      rootComposite = new Composite(parent, SWT.NONE);
      rootComposite.setLayout(new GridLayout(1, false));
      // progressComposite
      Composite progressComposite = new Composite(rootComposite, SWT.NONE);
      progressComposite.setLayout(new GridLayout(4, false));
      progressComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      Label proofLabel = new Label(progressComposite, SWT.NONE);
      proofLabel.setText("Proofs");
      proofProgressBar = new CustomProgressBar(progressComposite, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF, ProjectInfoColorTreeSynchronizer.COLOR_OPEN_PROOF);
      proofProgressBar.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      Label specificationLabel = new Label(progressComposite, SWT.NONE);
      specificationLabel.setText("Specifications");
      specificationProgressBar = new CustomProgressBar(progressComposite, ProjectInfoColorTreeSynchronizer.COLOR_CLOSED_PROOF, ProjectInfoColorTreeSynchronizer.COLOR_UNSPECIFIED);
      specificationProgressBar.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      // tabFolder
      CTabFolder tabFolder = new CTabFolder(rootComposite, SWT.FLAT | SWT.BOTTOM);
      tabFolder.setLayoutData(new GridData(GridData.FILL_BOTH));
      // treeViewrLegendComposite
      Composite treeViewrLegendComposite = new Composite(tabFolder, SWT.NONE);
      treeViewrLegendComposite.setLayout(new GridLayout(1, false));
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
      // legendComposite
      Composite legendComposite = new Composite(treeViewrLegendComposite, SWT.NONE);
      legendComposite.setLayout(new GridLayout(5, false));
      Label legendLabel = new Label(legendComposite, SWT.NONE);
      legendLabel.setText("Colors: ");
      legendLabel.setToolTipText("Colors indicate the verification status and parents are colored according to the worst verification stati of their children.");
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
      // assumptionText
      assumptionText = new Text(tabFolder, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL | SWT.MULTI);
      assumptionText.setEditable(false);
      // projectTabItem
      CTabItem assumptionTabItem = new CTabItem(tabFolder, SWT.NONE);
      assumptionTabItem.setText("&Assumptions");
      assumptionTabItem.setControl(assumptionText);
   }

   /**
    * Updates the shown content.
    */
   public void updateShownContent() {
      List<IProject> newProjects = computeProjectsToShow();
      if (projects == null || !projects.equals(newProjects)) {
         projects = newProjects;
         if (colorSynchronizer != null) {
            colorSynchronizer.dispose();
         }
         removeProjectInfoListener();
         projectInfos = new LinkedList<ProjectInfo>();
         for (IProject project : projects) {
            ProjectInfo info = ProjectInfoManager.getInstance().getProjectInfo(project);
            projectInfos.add(info);
            info.addProjectInfoListener(projectInfoListener);
         }
         labelProvider.setProjects(projects);
         treeViewer.setInput(projects);
         colorSynchronizer = new ProjectInfoColorTreeSynchronizer(projects, treeViewer);
      }
      updateProgressBarsAndAssumptions(); // Always update progress bars because method is called on any resource change
   }

   /**
    * Removes the listener from all {@link ProjectInfo}s in {@link #projectInfos}.
    */
   protected void removeProjectInfoListener() {
      if (projectInfos != null) {
         for (ProjectInfo info : projectInfos) {
            info.removeProjectInfoListener(projectInfoListener);
         }
         projectInfos = null;
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
    * Handles a double click.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      selectInWorkbench(event.getSelection());
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
         if (element instanceof ObserverFunctionInfo) {
            ObserverFunctionInfo info = (ObserverFunctionInfo) element;
            element = info.getParent();
         }
         // Try to select element
         if (element instanceof IProject) {
            WorkbenchUtil.selectAndReveal((IProject)element);
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
               if (info.getParent().getFile() != null) {
                  IEditorPart editor = WorkbenchUtil.openEditor(info.getParent().getFile());
                  if (editor instanceof JavaEditor) {
                     IMethod type = info.findJDTMethod();
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
   protected void updateProgressBarsAndAssumptions() {
      AbstractDependingOnObjectsJob.cancelJobs(VerificationStatusView.this);
      Job job = new AbstractDependingOnObjectsJob("Computing verification status", VerificationStatusView.this) {
         @Override
         protected IStatus run(IProgressMonitor monitor) {
            try {
               SWTUtil.checkCanceled(monitor);
               final VerificationStatus status = new VerificationStatus();
               if (projectInfos != null) {
                  for (ProjectInfo info : projectInfos) {
                     SWTUtil.checkCanceled(monitor);
                     updateStatus(info, status, monitor);
                  }
               }
               SWTUtil.checkCanceled(monitor);
               if (!proofProgressBar.isDisposed()) {
                  proofProgressBar.getDisplay().syncExec(new Runnable() {
                     @Override
                     public void run() {
                        proofProgressBar.setToolTipText(status.numOfProvenContracts + " of " + status.numOfContracts + " proof obligations are proven.");
                        proofProgressBar.reset(status.numOfProvenContracts != status.numOfContracts, false, status.numOfProvenContracts, status.numOfContracts);
                        specificationProgressBar.setToolTipText(status.numOfSpecifiedMethods + " of " + status.numOfMethods + " methods are specified.");
                        specificationProgressBar.reset(status.numOfSpecifiedMethods != status.numOfMethods, false, status.numOfSpecifiedMethods, status.numOfMethods);
                     }
                  });
               }
               SWTUtil.checkCanceled(monitor);
               final String assumptions = createAssumptionText(status, monitor);
               SWTUtil.checkCanceled(monitor);
               if (!assumptionText.isDisposed()) {
                  assumptionText.getDisplay().syncExec(new Runnable() {
                     @Override
                     public void run() {
                        assumptionText.setText(assumptions);
                     }
                  });
               }
               return Status.OK_STATUS;
            }
            catch (OperationCanceledException e) {
               return Status.CANCEL_STATUS;
            }
         }
         
         private String createAssumptionText(VerificationStatus status, IProgressMonitor monitor) {
            StringBuffer sb = new StringBuffer();
            sb.append("Proofs are performed under the following assumptions still needs to be proven:");
            sb.append(StringUtil.NEW_LINE);
            int i = 1;
            for (Entry<ProofMetaFileAssumption, List<IFile>> entry : status.assumptions.entrySet()) {
               sb.append(i);
               sb.append(": ");
               sb.append(entry.getKey());
               sb.append(StringUtil.NEW_LINE);
               for (IFile file : entry.getValue()) {
                  sb.append("\t - Used by proof: ");
                  sb.append(file.getFullPath());
                  sb.append(StringUtil.NEW_LINE);
               }
               i++;
            }
            sb.append(i);
            sb.append(": Java and JML semantics are correctly modeled in KeY.");
            sb.append(StringUtil.NEW_LINE);
            i++;
            sb.append(i);
            sb.append(": Source code is compiled using a correct Java compiler.");
            sb.append(StringUtil.NEW_LINE);
            i++;
            sb.append(i);
            sb.append(": Program is run on a a correct JVM.");
            sb.append(StringUtil.NEW_LINE);
            return sb.toString();
         }
         
         private void updateStatus(ProjectInfo projectInfo, VerificationStatus status, IProgressMonitor monitor) {
            for (PackageInfo packageInfo : projectInfo.getPackages()) {
               SWTUtil.checkCanceled(monitor);
               updateStatus(packageInfo, status, monitor);
            }
         }

         private void updateStatus(PackageInfo packageInfo, VerificationStatus status, IProgressMonitor monitor) {
            for (TypeInfo typeInfo : packageInfo.getTypes()) {
               SWTUtil.checkCanceled(monitor);
               updateStatus(typeInfo, status, monitor);
            }
         }

         private void updateStatus(TypeInfo typeInfo, VerificationStatus status, IProgressMonitor monitor) {
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

         private void updateStatus(ContractInfo contractInfo, VerificationStatus status) {
            status.numOfContracts++;
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
            try {
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
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e);
            }
         }
      };
      job.setSystem(true);
      job.schedule();
   }
   
   /**
    * Utility class used by {@link VerificationStatus#updateProgressBarsAndAssumptions()}
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
       * The made assumptions.
       */
      private final Map<ProofMetaFileAssumption, List<IFile>> assumptions = new LinkedHashMap<ProofMetaFileAssumption, List<IFile>>();
   }
   
   /**
    * When a new {@link TypeInfo} was added to the given {@link AbstractTypeContainer}.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param type The added {@link TypeInfo}.
    * @param index The index.
    */
   protected void handleTypeAdded(final AbstractTypeContainer tcInfo, final TypeInfo type, final int index) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When existing {@link TypeInfo}s were removed.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param types The removed {@link TypeInfo}s.
    */
   protected void handleTypesRemoved(final AbstractTypeContainer tcInfo, final Collection<TypeInfo> types) {
      updateProgressBarsAndAssumptions();
   }
   
   /**
    * When a new {@link MethodInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param method The added {@link MethodInfo}.
    * @param index The index.
    */
   protected void handleMethodAdded(final TypeInfo type, final MethodInfo method, final int index) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When existing {@link MethodInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param methods The removed {@link MethodInfo}s.
    */
   protected void handleMethodsRemoved(final TypeInfo type, final Collection<MethodInfo> methods) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When a new {@link ObserverFunctionInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunction The added {@link ObserverFunctionInfo}.
    * @param index The index.
    */
   protected void handleObserverFunctionAdded(final TypeInfo type, final ObserverFunctionInfo observerFunction, final int index) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When existing {@link ObserverFunctionInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunctions The removed {@link ObserverFunctionInfo}s.
    */
   protected void handleObserFunctionsRemoved(final TypeInfo type, final Collection<ObserverFunctionInfo> observerFunctions) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When a new {@link ContractInfo} was added to the given {@link AbstractContractContainer}.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contract The added {@link ContractInfo}.
    * @param index The index.
    */
   protected void handleContractAdded(final AbstractContractContainer cc, final ContractInfo contract, final int index) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When existing {@link ContractInfo}s were removed.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contracts The removed {@link ContractInfo}s.
    */
   protected void handleContractsRemoved(final AbstractContractContainer cc, final Collection<ContractInfo> contracts) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When a new {@link PackageInfo} was added to the given {@link ProjectInfo}.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packageInfo The added {@link PackageInfo}.
    * @param index The index.
    */
   protected void handlePackageAdded(final ProjectInfo projectInfo, final PackageInfo packageInfo, final int index) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When existing {@link PackageInfo}s were removed.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packages The removed {@link PackageInfo}s.
    */
   protected void handlePackagesRemoved(final ProjectInfo projectInfo, final Collection<PackageInfo> packages) {
      updateProgressBarsAndAssumptions();
   }

   /**
    * When some {@link IResource}s have changed.
    * @param event The {@link IResourceChangeEvent}.
    */
   protected void handleResourceChanged(IResourceChangeEvent event) {
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
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceChangeListener);
      removeProjectInfoListener();
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
      super.dispose();
   }
}
