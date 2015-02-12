package org.key_project.key4eclipse.resources.projectinfo;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;

/**
 * Provides the basic functionality to maintain contracts as known by KeY.
 * @author Martin Hentschel
 */
public abstract class AbstractContractContainer {
   /**
    * The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    */
   private final ProjectInfo projectInfo;
   
   /**
    * The contained {@link ContractInfo}s for quick access by their names.
    */
   private final Map<String, ContractInfo> contractsMap = new HashMap<String, ContractInfo>();

   /**
    * The contained {@link ContractInfo}s.
    */
   private final List<ContractInfo> contractsList = new LinkedList<ContractInfo>();
   
   /**
    * Constructor.
    * @param projectInfo The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    */
   public AbstractContractContainer(ProjectInfo projectInfo) {
      Assert.isNotNull(projectInfo);
      this.projectInfo = projectInfo;
   }

   /**
    * Returns the {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    * @return The {@link ProjectInfo} in which this {@link PackageInfo} is part of.
    */
   public ProjectInfo getProjectInfo() {
      return projectInfo;
   }

   /**
    * Adds the given {@link ContractInfo} at the given index.
    * @param contract The {@link ContractInfo} to add.
    * @param index The index to add {@link ContractInfo} at.
    */
   public void addContract(ContractInfo contract, int index) {
      if (contract != null) {
         contractsMap.put(contract.getName(), contract);
         contractsList.add(index, contract);
         projectInfo.mapResource(contract.getProofFile(), contract);
         projectInfo.mapResource(contract.getMetaFile(), contract);
         projectInfo.fireContractAdded(this, contract, index);
      }
   }
   
   /**
    * Returns all contained {@link ContractInfo}s.
    * @return All contained {@link ContractInfo}s.
    */
   public ContractInfo[] getContracts() {
      return contractsList.toArray(new ContractInfo[contractsList.size()]);
   }

   /**
    * Removes all given {@link ContractInfo}s.
    * @param contracts The {@link ContractInfo}s to remove.
    */
   public void removeContracts(Collection<ContractInfo> contracts) {
      if (contracts != null) {
         for (ContractInfo contract : contracts) {
            contractsMap.remove(contract.getName());
            projectInfo.unmapResource(contract.getProofFile(), contract);
            projectInfo.unmapResource(contract.getMetaFile(), contract);
         }
         contractsList.removeAll(contracts);
         projectInfo.fireContractsRemoved(this, contracts);
      }
   }

   /**
    * Searches the {@link ContractInfo} with the given name.
    * @param name The name.
    * @return The found {@link ContractInfo} or {@code null} if not available.
    */
   public ContractInfo getContract(String name) {
      return contractsMap.get(name);
   }

   /**
    * Counts the contained {@link ContractInfo}s.
    * @return The number of contained {@link ContractInfo}s.
    */
   public int countContracts() {
      return contractsMap.size();
   }

   /**
    * Returns the {@link ContractInfo} at the given index.
    * @param index The index of the requested {@link ContractInfo}.
    * @return The {@link ContractInfo} at the given index.
    */
   public ContractInfo getContract(int index) {
      return index >= 0 && index < contractsList.size() ? contractsList.get(index) : null;
   }

   /**
    * Returns the index of the given {@link ContractInfo}.
    * @param contract The {@link ContractInfo} for which its index is requested.
    * @return The index of the given {@link ContractInfo} or {@code -1} if not contained.
    */
   public int indexOfContract(ContractInfo contract) {
      return contractsList.indexOf(contract);
   }
}
