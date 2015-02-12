package org.key_project.key4eclipse.resources.projectinfo.event;

import java.util.Collection;
import java.util.EventListener;

import org.key_project.key4eclipse.resources.projectinfo.AbstractContractContainer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractTypeContainer;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;

/**
 * An event thrown from a {@link ProjectInfo}.
 * @author Martin Hentschel
 */
public interface IProjectInfoListener extends EventListener {
   /**
    * When a new {@link PackageInfo} was added to the given {@link ProjectInfo}.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packageInfo The added {@link PackageInfo}.
    * @param index The index.
    */
   public void packageAdded(ProjectInfo projectInfo, PackageInfo packageInfo, int index);

   /**
    * When existing {@link PackageInfo}s were removed.
    * @param projectInfo The modified {@link ProjectInfo}.
    * @param packages The removed {@link PackageInfo}s.
    */
   public void packagesRemoved(ProjectInfo projectInfo, Collection<PackageInfo> packages);
   
   /**
    * When a new {@link TypeInfo} was added to the given {@link AbstractTypeContainer}.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param type The added {@link TypeInfo}.
    * @param index The index.
    */
   public void typeAdded(AbstractTypeContainer tcInfo, TypeInfo type, int index);

   /**
    * When existing {@link TypeInfo}s were removed.
    * @param tcInfo The modified {@link AbstractTypeContainer}.
    * @param types The removed {@link TypeInfo}s.
    */
   public void typesRemoved(AbstractTypeContainer tcInfo, Collection<TypeInfo> types);

   /**
    * When a new {@link MethodInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param method The added {@link MethodInfo}.
    * @param index The index.
    */
   public void methodAdded(TypeInfo type, MethodInfo method, int index);

   /**
    * When existing {@link MethodInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param methods The removed {@link MethodInfo}s.
    */
   public void methodsRemoved(TypeInfo type, Collection<MethodInfo> methods);

   /**
    * When a new {@link ObserverFunctionInfo} was added to the given {@link TypeInfo}.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunction The added {@link ObserverFunctionInfo}.
    * @param index The index.
    */
   public void observerFunctionAdded(TypeInfo type, ObserverFunctionInfo observerFunction, int index);

   /**
    * When existing {@link ObserverFunctionInfo}s were removed.
    * @param type The modified {@link TypeInfo}.
    * @param observerFunctions The removed {@link ObserverFunctionInfo}s.
    */
   public void obserFunctionsRemoved(TypeInfo type, Collection<ObserverFunctionInfo> observerFunctions);

   /**
    * When a new {@link ContractInfo} was added to the given {@link AbstractContractContainer}.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contract The added {@link ContractInfo}.
    * @param index The index.
    */
   public void contractAdded(AbstractContractContainer cc, ContractInfo contract, int index);

   /**
    * When existing {@link ContractInfo}s were removed.
    * @param cc The modified {@link AbstractContractContainer}.
    * @param contracts The removed {@link ContractInfo}s.
    */
   public void contractsRemoved(AbstractContractContainer cc, Collection<ContractInfo> contracts);
}
