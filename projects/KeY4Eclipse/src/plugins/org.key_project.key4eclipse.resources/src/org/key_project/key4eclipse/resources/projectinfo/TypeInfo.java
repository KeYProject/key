package org.key_project.key4eclipse.resources.projectinfo;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;

/**
 * Represents a type as known by KeY.
 * @author Martin Hentschel
 */
public class TypeInfo extends AbstractTypeContainer implements IStatusInfo {
   /**
    * The name.
    */
   private final String name;
   
   /**
    * The {@link IFile} in eclipse which contains this type.
    */
   private final IFile file;
   
   /**
    * The parent {@link AbstractContractContainer} in which this {@link TypeInfo} is contained in.
    */
   private final AbstractTypeContainer parent;

   /**
    * The contained {@link MethodInfoInfo}s for quick access by their display names.
    */
   private final Map<String, MethodInfo> methodsMap = new HashMap<String, MethodInfo>();

   /**
    * The contained {@link MethodInfo}s.
    */
   private final List<MethodInfo> methodsList = new LinkedList<MethodInfo>();

   /**
    * The contained {@link ObserverFunctionInfo}s for quick access by their display names.
    */
   private final Map<String, ObserverFunctionInfo> observerFunctionsMap = new HashMap<String, ObserverFunctionInfo>();

   /**
    * The contained {@link ObserverFunctionInfo}s.
    */
   private final List<ObserverFunctionInfo> observerFunctionsList = new LinkedList<ObserverFunctionInfo>();

   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @param name The name.
    * @param file The {@link IFile} in eclipse which contains this type.
    * @param parent The parent {@link AbstractContractContainer} in which this {@link TypeInfo} is contained in.
    */
   public TypeInfo(ProjectInfo projectInfo, String name, IFile file, AbstractTypeContainer parent) {
      super(projectInfo);
      Assert.isNotNull(name);
      Assert.isNotNull(parent);
      this.name = name;
      this.file = file;
      this.parent = parent;
   }
   
   /**
    * Adds the given {@link MethodInfo} at the given index.
    * @param method The {@link MethodInfo} to add.
    * @param index The index to add {@link MethodInfo} at.
    */
   public void addMethod(MethodInfo method, int index) {
      if (method != null) {
         methodsMap.put(method.getDisplayName(), method);
         methodsList.add(index, method);
         getProjectInfo().mapResource(file, method);
         getProjectInfo().fireMethodAdded(this, method, index);
      }
   }
   
   /**
    * Adds the given {@link ObserverFunctionInfo} at the given index.
    * @param observerFunction The {@link ObserverFunctionInfo} to add.
    * @param index The index to add {@link ObserverFunctionInfo} at.
    */
   public void addObserverFunction(ObserverFunctionInfo observerFunction, int index) {
      if (observerFunction != null) {
         observerFunctionsMap.put(observerFunction.getDisplayName(), observerFunction);
         observerFunctionsList.add(index, observerFunction);
         getProjectInfo().fireObserverFunctionAdded(this, observerFunction, index);
      }
   }
   
   /**
    * Returns the name.
    * @return The name.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the {@link IFile} in eclipse which contains this type.
    * @return The {@link IFile} in eclipse which contains this type.
    */
   public IFile getFile() {
      return file;
   }

   /**
    * Returns the parent {@link AbstractContractContainer} in which this {@link TypeInfo} is contained in.
    * @return The parent {@link AbstractContractContainer} in which this {@link TypeInfo} is contained in.
    */
   public AbstractTypeContainer getParent() {
      return parent;
   }

   /**
    * Returns all contained {@link MethodInfo}s.
    * @return All contained {@link MethodInfo}s.
    */
   public MethodInfo[] getMethods() {
      return methodsList.toArray(new MethodInfo[methodsList.size()]);
   }
   
   /**
    * Returns all contained {@link ObserverFunctionInfo}s.
    * @return All contained {@link ObserverFunctionInfo}s.
    */
   public ObserverFunctionInfo[] getObserverFunctions() {
      return observerFunctionsList.toArray(new ObserverFunctionInfo[observerFunctionsList.size()]);
   }
   
   /**
    * Removes all given {@link MethodInfo}s.
    * @param methods The {@link MethodInfo}s to remove.
    */
   public void removeMethods(Collection<MethodInfo> methods) {
      if (methods != null) {
         for (MethodInfo method : methods) {
            methodsMap.remove(method.getDisplayName());
            getProjectInfo().unmapResource(file, method);
         }
         methodsList.removeAll(methods);
         getProjectInfo().fireMethodsRemoved(this, methods);
      }
   }
   
   /**
    * Removes all given {@link ObserverFunctionInfo}s.
    * @param observerFunctions The {@link ObserverFunctionInfo}s to remove.
    */
   public void removeObserverFunctions(Collection<ObserverFunctionInfo> observerFunctions) {
      if (observerFunctions != null) {
         for (ObserverFunctionInfo observerFunction : observerFunctions) {
            observerFunctionsMap.remove(observerFunction.getDisplayName());
         }
         observerFunctionsList.removeAll(observerFunctions);
         getProjectInfo().fireObserFunctionsRemoved(this, observerFunctions);
      }
   }

   /**
    * Searches the {@link MethodInfo} with the given display name.
    * @param displayName The display name.
    * @return The found {@link MethodInfo} or {@code null} if not available.
    */
   public MethodInfo getMethod(String displayName) {
      return methodsMap.get(displayName);
   }

   /**
    * Searches the {@link ObserverFunctionInfo} with the given display name.
    * @param displayName The display name.
    * @return The found {@link ObserverFunctionInfo} or {@code null} if not available.
    */
   public ObserverFunctionInfo getObserverFunction(String displayName) {
      return observerFunctionsMap.get(displayName);
   }

   /**
    * Counts the contained {@link MethodInfo}s.
    * @return The number of contained {@link MethodInfo}s.
    */
   public int countMethods() {
      return methodsMap.size();
   }

   /**
    * Counts the contained {@link ObserverFunctionInfo}s.
    * @return The number of contained {@link ObserverFunctionInfo}s.
    */
   public int countObserverFunctions() {
      return observerFunctionsMap.size();
   }

   /**
    * Returns the {@link MethodInfo} at the given index.
    * @param index The index of the requested {@link MethodInfo}.
    * @return The {@link MethodInfo} at the given index.
    */
   public MethodInfo getMethod(int index) {
      return index >= 0 && index < methodsList.size() ? methodsList.get(index) : null;
   }

   /**
    * Returns the {@link ObserverFunctionInfo} at the given index.
    * @param index The index of the requested {@link ObserverFunctionInfo}.
    * @return The {@link ObserverFunctionInfo} at the given index.
    */
   public ObserverFunctionInfo getObserverFunction(int index) {
      return index >= 0 && index < observerFunctionsList.size() ? observerFunctionsList.get(index) : null;
   }

   /**
    * Returns the index of the given {@link MethodInfo}.
    * @param method The {@link MethodInfo} for which its index is requested.
    * @return The index of the given {@link MethodInfo} or {@code -1} if not contained.
    */
   public int indexOfMethod(MethodInfo method) {
      return methodsList.indexOf(method);
   }

   /**
    * Returns the index of the given {@link ObserverFunctionInfo}.
    * @param observerFunction The {@link ObserverFunctionInfo} for which its index is requested.
    * @return The index of the given {@link ObserverFunctionInfo} or {@code -1} if not contained.
    */
   public int indexOfObserverFunction(ObserverFunctionInfo observerFunction) {
      return observerFunctionsList.indexOf(observerFunction);
   }
   
   /**
    * Tries to find the {@link IType} represented by this type.
    * @return The found {@link IType} or {@code null} if not available.
    */
   public IType findJDTType() {
      if (parent instanceof PackageInfo) {
         if (file != null && file.exists()) {
            ICompilationUnit compilationUnit = null;
            IJavaElement element = JavaCore.create(file);
            if (element instanceof ICompilationUnit) {
               compilationUnit = (ICompilationUnit)element;
            }
            if (compilationUnit != null) {
               return compilationUnit.getType(name);
            }
         }
      }
      else {
         IType parentJDTType = ((TypeInfo) parent).findJDTType();
         if (parentJDTType != null) {
            return parentJDTType.getType(name);
         }
      }
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isUnspecified() {
      boolean specified = true;
      MethodInfo[] methods = getMethods();
      int i = 0;
      while (specified && i < methods.length) {
         if (methods[i].isUnspecified()) {
            specified = false;
         }
         i++;
      }
      if (specified) {
         TypeInfo[] types = getTypes();
         i = 0;
         while (specified && i < types.length) {
            if (types[i].isUnspecified()) {
               specified = false;
            }
            i++;
         }
      }
      return !specified;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasOpenProof() {
      boolean allClosed = true;
      MethodInfo[] methods = getMethods();
      int i = 0;
      while (allClosed && i < methods.length) {
         if (methods[i].hasOpenProof()) {
            allClosed = false;
         }
         i++;
      }
      if (allClosed) {
         ObserverFunctionInfo[] observerFunctions = getObserverFunctions();
         i = 0;
         while (allClosed && i < observerFunctions.length) {
            if (observerFunctions[i].hasOpenProof()) {
               allClosed = false;
            }
            i++;
         }
      }
      if (allClosed) {
         TypeInfo[] types = getTypes();
         i = 0;
         while (allClosed && i < types.length) {
            if (types[i].hasOpenProof()) {
               allClosed = false;
            }
            i++;
         }
      }
      return !allClosed;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isPartOfRecursionCycle() {
      boolean partOfCycle = false;
      MethodInfo[] methods = getMethods();
      int i = 0;
      while (!partOfCycle && i < methods.length) {
         if (methods[i].isPartOfRecursionCycle()) {
            partOfCycle = true;
         }
         i++;
      }
      if (!partOfCycle) {
         ObserverFunctionInfo[] observerFunctions = getObserverFunctions();
         i = 0;
         while (!partOfCycle && i < observerFunctions.length) {
            if (observerFunctions[i].isPartOfRecursionCycle()) {
               partOfCycle = true;
            }
            i++;
         }
      }
      if (!partOfCycle) {
         TypeInfo[] types = getTypes();
         i = 0;
         while (!partOfCycle && i < types.length) {
            if (types[i].isPartOfRecursionCycle()) {
               partOfCycle = true;
            }
            i++;
         }
      }
      return partOfCycle;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasUnprovenDependencies() {
      boolean allDependeniesProven = true;
      MethodInfo[] methods = getMethods();
      int i = 0;
      while (allDependeniesProven && i < methods.length) {
         if (methods[i].hasUnprovenDependencies()) {
            allDependeniesProven = false;
         }
         i++;
      }
      if (allDependeniesProven) {
         ObserverFunctionInfo[] observerFunctions = getObserverFunctions();
         i = 0;
         while (allDependeniesProven && i < observerFunctions.length) {
            if (observerFunctions[i].hasUnprovenDependencies()) {
               allDependeniesProven = false;
            }
            i++;
         }
      }
      if (allDependeniesProven) {
         TypeInfo[] types = getTypes();
         i = 0;
         while (allDependeniesProven && i < types.length) {
            if (types[i].hasUnprovenDependencies()) {
               allDependeniesProven = false;
            }
            i++;
         }
      }
      return !allDependeniesProven;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return name;
   }
}
