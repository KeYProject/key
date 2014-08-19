package org.key_project.key4eclipse.resources.ui.provider;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo.ContractModality;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo.TacletOptionIssues;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.ui.util.ResourcesUiImages;
import org.key_project.util.java.CollectionUtil;

import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.ChoiceSelector.ChoiceEntry;
import de.uka.ilkd.key.proof.init.ProofInputException;

/**
 * An {@link ILabelProvider} to label {@link ProjectInfo}s and its content
 * in a {@link Viewer}.
 * @author Martin Hentschel
 */
public class ProjectInfoLabelProvider extends ColumnLabelProvider {
   /**
    * The {@link Viewer} in which this {@link ILabelProvider} is used.
    */
   private final Viewer viewer;
   
   /**
    * The currently shown {@link IProject}s.
    */
   private List<IProject> projects;
   
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
    * Constructor.
    */
   public ProjectInfoLabelProvider(Viewer viewer) {
      Assert.isNotNull(viewer);
      this.viewer = viewer;
      ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceChangeListener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      ResourcesPlugin.getWorkspace().removeResourceChangeListener(resourceChangeListener);
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      try {
         if (element instanceof IProject) {
            return ((IProject) element).getName();
         }
         else if (element instanceof PackageInfo) {
            PackageInfo packageInfo = (PackageInfo) element; 
            IPackageFragment packageFragment = packageInfo.findJDTPackage();
            if (packageFragment != null && packageFragment.exists()) {
               return WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getText(packageFragment);
            }
            else {
               return packageInfo.getName();
            }
         }
         else if (element instanceof TypeInfo) {
            TypeInfo typeInfo = (TypeInfo) element; 
            IType javaType = typeInfo.findJDTType();
            if (javaType != null && javaType.exists()) {
               return WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getText(javaType);
            }
            else {
               return typeInfo.getName();
            }
         }
         else if (element instanceof MethodInfo) {
            MethodInfo methodInfo = (MethodInfo) element; 
            IMethod javaMethod = methodInfo.findJDTMethod();
            if (javaMethod != null && javaMethod.exists()) {
               return WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getText(javaMethod);
            }
            else {
               return methodInfo.getDisplayName();
            }
         }
         else if (element instanceof ObserverFunctionInfo) {
            return ((ObserverFunctionInfo) element).getDisplayName();
         }
         else if (element instanceof ContractInfo) {
            return ((ContractInfo) element).getName();
         }
         else {
            return null;
         }
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
         return e.getMessage();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      try {
         Image image;
         if (element instanceof IProject) {
            image = WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getImage(element);
         }
         else if (element instanceof PackageInfo) {
            PackageInfo packageInfo = (PackageInfo) element; 
            IPackageFragment packageFragment = packageInfo.findJDTPackage();
            if (packageFragment != null && packageFragment.exists()) {
               image = WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getImage(packageFragment);
            }
            else {
               image = WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getImage(packageInfo.getContainer());
            }
         }
         else if (element instanceof TypeInfo) {
            TypeInfo typeInfo = (TypeInfo) element; 
            IType javaType = typeInfo.findJDTType();
            if (javaType != null && javaType.exists()) {
               image = WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getImage(javaType);
            }
            else {
               image = WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getImage(typeInfo.getFile());
            }
         }
         else if (element instanceof MethodInfo) {
            MethodInfo methodInfo = (MethodInfo) element; 
            IMethod javaMethod = methodInfo.findJDTMethod();
            if (javaMethod != null && javaMethod.exists()) {
               image = WorkbenchLabelProvider.getDecoratingWorkbenchLabelProvider().getImage(javaMethod);
            }
            else {
               image = null;
            }
         }
         else if (element instanceof ObserverFunctionInfo) {
            image = ResourcesUiImages.getImage(ResourcesUiImages.OBSERVER_FUNCTION);
         }
         else if (element instanceof ContractInfo) {
            ContractInfo ci = (ContractInfo) element;
            TacletOptionIssues tacletIssues;
            try {
               tacletIssues = ci.checkTaletOptions();
            }
            catch (ProofInputException e) {
               LogUtil.getLogger().logError(e);
               tacletIssues = null;
            }
            if (ci.getParent() instanceof MethodInfo) {
               if (tacletIssues != null && !tacletIssues.getUnsoundOptions().isEmpty()) {
                  if (ContractModality.BOX.equals(ci.getModality())) {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_BOX_WARNING);
                  }
                  else if (ContractModality.DIAMOND.equals(ci.getModality())) {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_DIAMOND_WARNING);
                  }
                  else {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_WARNING);
                  }
               }
               else if (tacletIssues != null && !tacletIssues.getIncompleteOptions().isEmpty()) {
                  if (ContractModality.BOX.equals(ci.getModality())) {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_BOX_INFO);
                  }
                  else if (ContractModality.DIAMOND.equals(ci.getModality())) {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_DIAMOND_INFO);
                  }
                  else {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_INFO);
                  }
               }
               else {
                  if (ContractModality.BOX.equals(ci.getModality())) {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_BOX);
                  }
                  else if (ContractModality.DIAMOND.equals(ci.getModality())) {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT_DIAMOND);
                  }
                  else {
                     image = ResourcesUiImages.getImage(ResourcesUiImages.METHOD_CONTRACT);
                  }
               }
            }
            else {
               if (tacletIssues != null && !tacletIssues.getUnsoundOptions().isEmpty()) {
                  image = ResourcesUiImages.getImage(ResourcesUiImages.OBSERVER_FUNCTION_CONTRACT_WARNING);
               }
               else if (tacletIssues != null && !tacletIssues.getIncompleteOptions().isEmpty()) {
                  image = ResourcesUiImages.getImage(ResourcesUiImages.OBSERVER_FUNCTION_CONTRACT_INFO);
               }
               else {
                  image = ResourcesUiImages.getImage(ResourcesUiImages.OBSERVER_FUNCTION_CONTRACT);
               }
            }
         }
         else {
            image = null;
         }
         if (image != null) {
            return image;
         }
         else {
            return ResourcesUiImages.getImage(ResourcesUiImages.UNKNOWN_ELEMENT);
         }
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getToolTipText(Object element) {
      if (element instanceof ContractInfo) {
         try {
            StringBuffer sb = new StringBuffer();
            ContractInfo info = (ContractInfo) element;
            // Add information about cyclic specification use
            List<IFile> cycle = info.checkProofRecursionCycle();
            if (!CollectionUtil.isEmpty(cycle)) {
               sb.append("Cyclic use of specifications:\n");
               for (IFile file : cycle) {
                  sb.append("- " + file.getFullPath() + "\n");
               }
            }
            // Add information about unproven proof dependencies
            List<IFile> unprovenProofs = info.checkUnprovenDependencies();
            if (unprovenProofs != null && !unprovenProofs.isEmpty()) {
               sb.append("Unproven Dependency:\n");
               for (IFile unprovenProof : unprovenProofs) {
                  sb.append("- " + unprovenProof.getFullPath() + "\n");
               }
            }
            // Add information about taclet options
            TacletOptionIssues tacletIssues = info.checkTaletOptions();
            if (tacletIssues != null && 
                (!tacletIssues.getIncompleteOptions().isEmpty() || !tacletIssues.getUnsoundOptions().isEmpty() || !tacletIssues.getInformationOptions().isEmpty())) {
               if (sb.length() >= 1) {
                  sb.append("\n");
               }
               sb.append("Taclet Options:");
               for (String value : tacletIssues.getUnsoundOptions()) {
                  if (sb.length() >= 1) {
                     sb.append("\n");
                  }
                  sb.append("- " + value + ": " + ChoiceEntry.UNSOUND_TEXT);
               }
               for (String value : tacletIssues.getIncompleteOptions()) {
                  if (sb.length() >= 1) {
                     sb.append("\n");
                  }
                  sb.append("- " + value + ": " + ChoiceEntry.INCOMPLETE_TEXT);
               }
               for (String value : tacletIssues.getInformationOptions()) {
                  if (sb.length() >= 1) {
                     sb.append("\n");
                  }
                  sb.append("- " + value + ": " + ChoiceSelector.getInformation(value));
               }
            }
            return sb.length() == 0 ? null : sb.toString();
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * When some {@link IResource}s have changed.
    * @param event The {@link IResourceChangeEvent}.
    */
   protected void handleResourceChanged(IResourceChangeEvent event) {
      final List<Object> modelElements = new LinkedList<Object>();
      collectModelElements(event.getDelta(), modelElements);
      if (!modelElements.isEmpty()) {
         if (!viewer.getControl().isDisposed()) {
            viewer.getControl().getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  fireLabelProviderChanged(new LabelProviderChangedEvent(ProjectInfoLabelProvider.this, modelElements.toArray()));
               }
            });
         }
      }
   }

   /**
    * Collects all model elements in the given {@link IResourceDelta} and its children.
    * @param delta The {@link IResourceDelta}.
    * @param toFill The {@link List} to fill with model elements.
    */
   protected void collectModelElements(IResourceDelta delta, List<Object> toFill) {
      if (delta != null) {
         IResource resource = delta.getResource();
         Set<Object> elements = getModelElements(resource);
         if (elements != null) {
            toFill.addAll(elements);
         }
         for (IResourceDelta childDelta : delta.getAffectedChildren()) {
            collectModelElements(childDelta, toFill);
         }
      }
   }

   /**
    * Returns all model elements for the given {@link IResource}.
    * @param resource The {@link IResource} for which model elements are requested.
    * @return The found model elements or {@code null} if not available.
    */
   protected Set<Object> getModelElements(IResource resource) {
      if (projects != null) {
         Set<Object> result = new HashSet<Object>();
         for (IProject project : projects) {
            ProjectInfo info = ProjectInfoManager.getInstance().getProjectInfo(project);
            Set<Object> modelElements = info.getModelElements(resource);
            if (modelElements != null) {
               result.addAll(modelElements);
            }
         }
         return result;
      }
      else {
         return null;
      }
   }

   /**
    * Returns the currently shown {@link IProject}s.
    * @return The currently shown {@link IProject}s.
    */
   public List<IProject> getProjects() {
      return projects;
   }

   /**
    * Sets the {@link IProject}s to show.
    * @param projects The {@link IProject}s to show.
    */
   public void setProjects(List<IProject> projects) {
      this.projects = projects;
   }
}
