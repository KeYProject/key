package org.key_project.key4eclipse.resources.ui.provider;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.ui.services.IDisposable;
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

/**
 * Provides the basic functionality to observe multiple {@link ProjectInfo}s.
 * @author Martin Hentschel
 */
public abstract class AbstractProjectInfoBasedContent implements IDisposable {
   /**
    * Listens for changes on a {@link ProjectInfo}.
    */
   private final IProjectInfoListener listener = new IProjectInfoListener() {
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
    * All observed {@link ProjectInfo}s.
    */
   private Map<ProjectInfo, IProject> observedInfos;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      removeProjectInfoListener();
   }

   /**
    * Removes the listener from all observed {@link ProjectInfo}s.
    */
   protected void removeProjectInfoListener() {
      if (observedInfos != null) {
         for (ProjectInfo info : observedInfos.keySet()) {
            info.removeProjectInfoListener(listener);
         }
         observedInfos = null;
      }
   }
   
   /**
    * Adds the listener to all {@link ProjectInfo}s of the {@link IProject}s
    * in the given {@link List}.
    * @param input The {@link List} which provides the {@link IProject}s to observe their {@link ProjectInfo}s.
    */
   protected void addProjectInfoListener(Object input) {
      if (input instanceof List<?>) {
         List<?> list = (List<?>)input;
         observedInfos = new HashMap<ProjectInfo, IProject>();
         for (Object element : list) {
            if (element instanceof IProject) {
               IProject project = (IProject)element;
               ProjectInfo info = ProjectInfoManager.getInstance().getProjectInfo(project);
               observedInfos.put(info, project);
               info.addProjectInfoListener(listener);
            }
         }
      }
   }
   
   /**
    * Returns the {@link IProject} of the given {@link ProjectInfo}.
    * @param projectInfo The {@link ProjectInfo}.
    * @return The {@link IProject} if known or {@code null} otherwise.
    */
   protected IProject getProject(ProjectInfo projectInfo) {
      return observedInfos.get(projectInfo);
   }

   /**
    * Returns all model elements of the given {@link IResource}.
    * @param resource The {@link IResource}.
    * @return The known model elements or {@code null} otherwise.
    */
   protected Set<Object> getModelElements(IResource resource) {
      Set<Object> result = new HashSet<Object>();
      if (observedInfos != null) {
         for (ProjectInfo info : observedInfos.keySet()) {
            Set<Object> infoResult = info.getModelElements(resource);
            if (infoResult != null) {
               result.addAll(infoResult);
            }
         }
      }
      return result;
   }
   
   /**
    * When a new {@link TypeInfo} was added to the given {@link AbstractTypeContainer}.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param type The added {@link TypeInfo}.
    * @param index The index.
    */
   protected void handleTypeAdded(final AbstractTypeContainer tcInfo, final TypeInfo type, final int index) {
   }

   /**
    * When existing {@link TypeInfo}s were removed.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param types The removed {@link TypeInfo}s.
    */
   protected void handleTypesRemoved(final AbstractTypeContainer tcInfo, final Collection<TypeInfo> types) {
   }
   
   /**
    * When a new {@link MethodInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param method The added {@link MethodInfo}.
    * @param index The index.
    */
   protected void handleMethodAdded(final TypeInfo type, final MethodInfo method, final int index) {
   }

   /**
    * When existing {@link MethodInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param methods The removed {@link MethodInfo}s.
    */
   protected void handleMethodsRemoved(final TypeInfo type, final Collection<MethodInfo> methods) {
   }

   /**
    * When a new {@link ObserverFunctionInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunction The added {@link ObserverFunctionInfo}.
    * @param index The index.
    */
   protected void handleObserverFunctionAdded(final TypeInfo type, final ObserverFunctionInfo observerFunction, final int index) {
   }

   /**
    * When existing {@link ObserverFunctionInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunctions The removed {@link ObserverFunctionInfo}s.
    */
   protected void handleObserFunctionsRemoved(final TypeInfo type, final Collection<ObserverFunctionInfo> observerFunctions) {
   }

   /**
    * When a new {@link ContractInfo} was added to the given {@link AbstractContractContainer}.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contract The added {@link ContractInfo}.
    * @param index The index.
    */
   protected void handleContractAdded(final AbstractContractContainer cc, final ContractInfo contract, final int index) {
   }

   /**
    * When existing {@link ContractInfo}s were removed.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contracts The removed {@link ContractInfo}s.
    */
   protected void handleContractsRemoved(final AbstractContractContainer cc, final Collection<ContractInfo> contracts) {
   }

   /**
    * When a new {@link PackageInfo} was added to the given {@link ProjectInfo}.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packageInfo The added {@link PackageInfo}.
    * @param index The index.
    */
   protected void handlePackageAdded(final ProjectInfo projectInfo, final PackageInfo packageInfo, final int index) {
   }

   /**
    * When existing {@link PackageInfo}s were removed.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packages The removed {@link PackageInfo}s.
    */
   protected void handlePackagesRemoved(final ProjectInfo projectInfo, final Collection<PackageInfo> packages) {
   }
}
