package org.key_project.key4eclipse.resources.projectinfo;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.resources.projectinfo.event.IProjectInfoListener;

/**
 * <p>
 * Contains the source code structure of an {@link IProject} as known by KeY.
 * This is achieved with the following model objects:
 * <ul>
 *    <li>{@link ProjectInfo}</li>
 *    <li>{@link PackageInfo}</li>
 *    <li>{@link TypeInfo}</li>
 *    <li>{@link MethodInfo}</li>
 *    <li>{@link ObserverFunctionInfo}</li>
 *    <li>{@link ContractInfos}</li>
 * </ul>
 * </p>
 * <p>
 * Changes can be observed at the root {@link ProjectInfo} via an {@link IProjectInfoListener}.
 * </p>
 * @author Martin Hentschel
 * @see PackageInfo
 * @see TypeInfo
 * @see MethodInfo
 * @see ObserverFunctionInfo
 * @see ContractInfo
 */
public class ProjectInfo {
   /**
    * All available {@link IProjectInfoListener}.
    */
   private final List<IProjectInfoListener> listener = new LinkedList<IProjectInfoListener>();
   
   /**
    * The contained {@link PackageInfo}s.
    */
   private final List<PackageInfo> packageList = new LinkedList<PackageInfo>();
   
   /**
    * The contained {@link PackageInfo}s for quick access by their names.
    */
   private final Map<String, PackageInfo> packagesMap = new HashMap<String, PackageInfo>();
   
   /**
    * Maps an {@link IResource} to all its model elements, e.g.
    * {@link PackageInfo}, {@link TypeInfo}, {@link MethodInfo} and {@link ContractInfo}.
    */
   private final Map<IResource, Set<Object>> resourceToModelMap = new HashMap<IResource, Set<Object>>();
   
   /**
    * The {@link IProject}.
    */
   private final IProject project;
   
   /**
    * Constructor.
    * @param project The {@link IProject}.
    */
   public ProjectInfo(IProject project) {
      Assert.isNotNull(project);
      this.project = project;
   }

   /**
    * Adds the given {@link PackageInfo} at the given index.
    * @param packageInfo The {@link PackageInfo} to add.
    * @param index The index to add {@link PackageInfo} at.
    */
   public void addPackage(PackageInfo packageInfo, int index) {
      if (packageInfo != null) {
         packagesMap.put(packageInfo.getName(), packageInfo);
         packageList.add(index, packageInfo);
         mapResource(packageInfo.getContainer(), packageInfo);
         firePackageAdded(this, packageInfo, index);
      }
   }

   /**
    * Returns all contained {@link PackageInfo}s.
    * @return All contained {@link PackageInfo}s.
    */
   public PackageInfo[] getPackages() {
      return packageList.toArray(new PackageInfo[packageList.size()]);
   }
   
   /**
    * Searches the {@link PackageInfo} with the given name.
    * @param name The name.
    * @return The found {@link PackageInfo} or {@code null} if not available.
    */
   public PackageInfo getPackage(String name) {
      return packagesMap.get(name);
   }

   /**
    * Removes all given {@link PackageInfo}s.
    * @param packages The {@link PackageInfo}s to remove.
    */
   public void removePackages(Collection<PackageInfo> packages) {
      if (packages != null) {
         for (PackageInfo packageInfo : packages) {
            packagesMap.remove(packageInfo.getName());
            unmapResource(packageInfo.getContainer(), packageInfo);
         }
         packageList.removeAll(packages);
         firePackagesRemoved(this, packages);
      }
   }

   /**
    * Counts the contained {@link PackageInfo}s.
    * @return The number of contained {@link PackageInfo}s.
    */
   public int countPackages() {
      return packagesMap.size();
   }

   /**
    * Returns the {@link PackageInfo} at the given index.
    * @param index The index of the requested {@link PackageInfo}.
    * @return The {@link PackageInfo} at the given index.
    */
   public PackageInfo getPackage(int index) {
      return index >= 0 && index < packageList.size() ? packageList.get(index) : null;
   }

   /**
    * Returns the index of the given {@link PackageInfo}.
    * @param packageInfo The {@link PackageInfo} for which its index is requested.
    * @return The index of the given {@link PackageInfo} or {@code -1} if not contained.
    */
   public int indexOfPackage(PackageInfo packageInfo) {
      return packageList.indexOf(packageInfo);
   }
   
   /**
    * Adds the given {@link IProjectInfoListener}.
    * @param l The {@link IProjectInfoListener} to add.
    */
   public void addProjectInfoListener(IProjectInfoListener l) {
      if (l != null) {
         listener.add(l);
      }
   }
   
   /**
    * Removes the given {@link IProjectInfoListener}.
    * @param l The {@link IProjectInfoListener} to remove.
    */
   public void removeProjectInfoListener(IProjectInfoListener l) {
      if (l != null) {
         listener.remove(l);
      }
   }
   
   /**
    * Returns all registered {@link IProjectInfoListener}.
    * @return The registered {@link IProjectInfoListener}.
    */
   public IProjectInfoListener[] getProjectInfoListeners() {
      return listener.toArray(new IProjectInfoListener[listener.size()]);
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#typeAdded(AbstractTypeContainer, TypeInfo, int)} to all listener.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param type The added {@link TypeInfo}.
    * @param index The index.
    */
   protected void fireTypeAdded(AbstractTypeContainer tcInfo, TypeInfo type, int index) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.typeAdded(tcInfo, type, index);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#typesRemoved(AbstractTypeContainer, Collection)} to all listener.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param types The removed {@link TypeInfo}s.
    */
   protected void fireTypesRemoved(AbstractTypeContainer tcInfo, Collection<TypeInfo> types) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.typesRemoved(tcInfo, types);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#packageAdded(ProjectInfo, PackageInfo, int)} to all listener.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packageInfo The added {@link PackageInfo}.
    * @param index The index.
    */
   protected void firePackageAdded(ProjectInfo projectInfo, PackageInfo packageInfo, int index) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.packageAdded(projectInfo, packageInfo, index);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#packagesRemoved(ProjectInfo, Collection)} to all listener.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packages The removed {@link PackageInfo}s.
    */
   protected void firePackagesRemoved(ProjectInfo projectInfo, Collection<PackageInfo> packages) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.packagesRemoved(projectInfo, packages);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#methodAdded(TypeInfo, MethodInfo, int)} to all listener.
    * @param type The modified {@link TypeInfo}.
    * @param method The added {@link MethodInfo}.
    * @param index The index.
    */
   protected void fireMethodAdded(TypeInfo type, MethodInfo method, int index) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.methodAdded(type, method, index);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#methodsRemoved(TypeInfo, Collection)} to all listener.
    * @param type The modified {@link TypeInfo}.
    * @param methods The removed {@link MethodInfo}s.
    */
   protected void fireMethodsRemoved(TypeInfo type, Collection<MethodInfo> methods) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.methodsRemoved(type, methods);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#observerFunctionAdded(TypeInfo, ObserverFunctionInfo, int)} to all listener.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunction The added {@link ObserverFunctionInfo}.
    * @param index The index.
    */
   protected void fireObserverFunctionAdded(TypeInfo type, ObserverFunctionInfo observerFunction, int index) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.observerFunctionAdded(type, observerFunction, index);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#obserFunctionsRemoved(TypeInfo, Collection)} to all listener.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunctions The removed {@link ObserverFunctionInfo}s.
    */
   protected void fireObserFunctionsRemoved(TypeInfo type, Collection<ObserverFunctionInfo> observerFunctions) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.obserFunctionsRemoved(type, observerFunctions);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#contractAdded(AbstractContractContainer, ContractInfo, int)} to all listener.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contract The added {@link ContractInfo}.
    * @param index The index.
    */
   protected void fireContractAdded(AbstractContractContainer cc, ContractInfo contract, int index) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.contractAdded(cc, contract, index);
      }
   }
   
   /**
    * Fires the even {@link IProjectInfoListener#contractsRemoved(AbstractContractContainer, Collection)} to all listener.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contracts The removed {@link ContractInfo}s.
    */
   protected void fireContractsRemoved(AbstractContractContainer cc, Collection<ContractInfo> contracts) {
      IProjectInfoListener[] toInform = getProjectInfoListeners();
      for (IProjectInfoListener l : toInform) {
         l.contractsRemoved(cc, contracts);
      }
   }
   
   /**
    * Maps the {@link IResource} to the given model object.
    * @param resource The {@link IResource} to map.
    * @param model The target model object to map to.
    */
   public void mapResource(IResource resource, Object model) {
      if (resource != null && model != null) {
         Set<Object> modelList = resourceToModelMap.get(resource);
         if (modelList == null) {
            modelList = new HashSet<Object>();
            resourceToModelMap.put(resource, modelList);
         }
         modelList.add(model);
      }
   }
   
   /**
    * Unmaps the given model object from the given {@link IResource}.
    * @param resource The {@link IResource} to unmap model object from.
    * @param model The model object to unmap.
    */
   public void unmapResource(IResource resource, Object model) {
      if (resource != null && model != null) {
         Set<Object> modelList = resourceToModelMap.get(resource);
         if (modelList != null) {
            modelList.remove(model);
            if (modelList.isEmpty()) {
               resourceToModelMap.remove(resource);
            }
         }
      }
   }

   /**
    * Returns all model elements for the given {@link IResource}.
    * @param resource The {@link IResource} for which model elements are requested.
    * @return The found model elements or {@code null} if not available.
    */
   public Set<Object> getModelElements(IResource resource) {
      return resourceToModelMap.get(resource);
   }

   /**
    * Returns the {@link IProject}.
    * @return The {@link IProject}.
    */
   public IProject getProject() {
      return project;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return project.getName();
   }
}
