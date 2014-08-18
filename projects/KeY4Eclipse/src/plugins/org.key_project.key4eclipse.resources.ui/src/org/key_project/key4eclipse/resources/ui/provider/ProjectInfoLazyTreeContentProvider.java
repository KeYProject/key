package org.key_project.key4eclipse.resources.ui.provider;

import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractContractContainer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractTypeContainer;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;

/**
 * An {@link ILazyTreeContentProvider} which allows to show multiple {@link ProjectInfo}s
 * and their content in a {@link TreeViewer}.
 * @author Martin Hentschel
 */
public class ProjectInfoLazyTreeContentProvider extends AbstractProjectInfoBasedContent implements ILazyTreeContentProvider {
   /**
    * The {@link TreeViewer} in which this {@link ILazyTreeContentProvider} is used.
    */
   private TreeViewer viewer;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      Assert.isTrue(viewer instanceof TreeViewer);
      this.viewer = (TreeViewer)viewer;
      removeProjectInfoListener();
      addProjectInfoListener(newInput);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateElement(Object parent, int index) {
      Object element = null;
      if (parent instanceof List<?>) {
         List<?> list = (List<?>)parent;
         element = list.get(index);
      }
      else if (parent instanceof IProject) {
         ProjectInfo info = ProjectInfoManager.getInstance().getProjectInfo((IProject)parent);
         element = info.getPackage(index);
      }
      else if (parent instanceof PackageInfo) {
         element = ((PackageInfo) parent).getType(index);
      }
      else if (parent instanceof TypeInfo) {
         TypeInfo info = (TypeInfo)parent;
         int methodCount = info.countMethods();
         if (index < methodCount) {
            element = info.getMethod(index);
         }
         else {
            int observerFunctionsCount = info.countObserverFunctions();
            if (index < observerFunctionsCount + methodCount) {
               element = info.getObserverFunction(index - methodCount);
            }
            else {
               element = info.getType(index - methodCount - observerFunctionsCount);
            }
         }
      }
      else if (parent instanceof AbstractContractContainer) {
         AbstractContractContainer info = (AbstractContractContainer)parent;
         element = info.getContract(index);
      }
      if (element != null) {
         viewer.replace(parent, index, element);
         updateChildCount(element, -1);
      }
      else {
         updateChildCount(parent, -1);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateChildCount(Object element, int currentChildCount) {
      if (element instanceof List<?>) {
         List<?> list = (List<?>)element;
         viewer.setChildCount(element, list.size());
      }
      else if (element instanceof IProject) {
         ProjectInfo info = ProjectInfoManager.getInstance().getProjectInfo((IProject)element);
         viewer.setChildCount(element, info.countPackages());
      }
      else if (element instanceof PackageInfo) {
         PackageInfo info = (PackageInfo)element;
         viewer.setChildCount(element, info.countTypes());
      }
      else if (element instanceof TypeInfo) {
         TypeInfo info = (TypeInfo)element;
         viewer.setChildCount(element, info.countMethods() + info.countObserverFunctions() + info.countTypes());
      }
      else if (element instanceof AbstractContractContainer) {
         AbstractContractContainer info = (AbstractContractContainer)element;
         viewer.setChildCount(element, info.countContracts());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getParent(Object element) {
      return null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleTypeAdded(final AbstractTypeContainer tcInfo, final TypeInfo type, final int index) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            if (tcInfo instanceof TypeInfo) {
               TypeInfo typeInfo = (TypeInfo) tcInfo;
               viewer.insert(tcInfo, type, index + typeInfo.countMethods() + typeInfo.countObserverFunctions());
            }
            else {
               viewer.insert(tcInfo, type, index);
            }
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleTypesRemoved(final AbstractTypeContainer tcInfo, final Collection<TypeInfo> types) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            viewer.remove(tcInfo, types.toArray());
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleMethodAdded(final TypeInfo type, final MethodInfo method, final int index) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            viewer.insert(type, method, index);
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleMethodsRemoved(final TypeInfo type, final Collection<MethodInfo> methods) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            viewer.remove(type, methods.toArray());
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleObserverFunctionAdded(final TypeInfo type, final ObserverFunctionInfo observerFunction, final int index) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            viewer.insert(type, observerFunction, type.countMethods() + index);
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleObserFunctionsRemoved(final TypeInfo type, final Collection<ObserverFunctionInfo> observerFunctions) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            viewer.remove(type, observerFunctions.toArray());
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleContractAdded(final AbstractContractContainer cc, final ContractInfo contract, final int index) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            viewer.insert(cc, contract, index);
         }
      });      
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleContractsRemoved(final AbstractContractContainer cc, final Collection<ContractInfo> contracts) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            viewer.remove(cc, contracts.toArray());
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePackageAdded(final ProjectInfo projectInfo, final PackageInfo packageInfo, final int index) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            IProject project = getProject(projectInfo);
            Assert.isNotNull(project);
            viewer.insert(project, packageInfo, index);
         }
      });      
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handlePackagesRemoved(final ProjectInfo projectInfo, final Collection<PackageInfo> packages) {
      viewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            IProject project = getProject(projectInfo);
            Assert.isNotNull(project);
            viewer.remove(project, packages.toArray());
         }
      });
   }
}
