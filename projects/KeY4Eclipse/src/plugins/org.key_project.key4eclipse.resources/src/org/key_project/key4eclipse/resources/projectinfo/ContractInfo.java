package org.key_project.key4eclipse.resources.projectinfo;

import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileAssumption;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * Represents a contract as known by KeY.
 * @author Martin Hentschel
 */
public class ContractInfo {
   /**
    * The parent {@link AbstractContractContainer} in which this {@link ContractInfo} is contained in.
    */
   private final AbstractContractContainer parent;

   /**
    * The name.
    */
   private final String name;

   /**
    * Optionally the modality.
    */
   private final ContractModality modality;
   
   /**
    * The proof file.
    */
   private final IFile proofFile;
   
   /**
    * The meta file.
    */
   private final IFile metaFile;

   /**
    * Constructor.
    * @param parent The parent {@link AbstractContractContainer} in which this {@link ContractInfo} is contained in.
    * @param name The name.
    * @param modality The optional modality.
    * @param proofFile The proof file.
    * @param metaFilee The meta file.
    */
   public ContractInfo(AbstractContractContainer parent, String name, ContractModality modality, IFile proofFile, IFile metaFile) {
      Assert.isNotNull(parent);
      Assert.isNotNull(name);
      Assert.isNotNull(proofFile);
      Assert.isNotNull(metaFile);
      this.name = name;
      this.parent = parent;
      this.modality = modality;
      this.proofFile = proofFile;
      this.metaFile = metaFile;
   }

   /**
    * Returns the name.
    * @return The name.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the parent {@link AbstractContractContainer} in which this {@link ContractInfo} is contained in.
    * @return The parent {@link AbstractContractContainer} in which this {@link ContractInfo} is contained in.
    */
   public AbstractContractContainer getParent() {
      return parent;
   }
   
   /**
    * Returns the optional modality.
    * @return The optional modality or {@code null} if not defined.
    */
   public ContractModality getModality() {
      return modality;
   }

   /**
    * Returns the proof file.
    * @return The proof file.
    */
   public IFile getProofFile() {
      return proofFile;
   }
   
   /**
    * Returns the meta file.
    * @return The meta file.
    */
   public IFile getMetaFile() {
      return metaFile;
   }

   /**
    * Checks if the object itself or one of its children has an open proof.
    * @return {@code true} open proof contained, {@code false} everything is successful proven or {@code null} if unknown.
    */
   public Boolean checkProofClosed() throws CoreException {
      return KeYResourcesUtil.isProofClosed(proofFile);
   }
   
   /**
    * Checks if the current proof is based on unproven specifications.
    * @return {@code true} proof is based on unproven specifications, {@code false} all used specifications are proven or {@code null} if required meta file does not exist.
    * @throws Exception
    */
   public Boolean checkUnprovenDependencies() throws Exception {
      if (metaFile != null && metaFile.exists()) {
         ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
         List<IFile> dependingProofs = pmfr.getUsedContracts();
         if (dependingProofs != null && !dependingProofs.isEmpty()) {
            boolean allProven = true;
            Iterator<IFile> iter = dependingProofs.iterator();
            while (allProven && iter.hasNext()) {
               Boolean closed = KeYResourcesUtil.isProofClosed(iter.next());
               if (closed == null || !closed.booleanValue()) {
                  allProven = false;
               }
            }
            return Boolean.valueOf(!allProven);
         }
         else {
            return Boolean.FALSE;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Tries to read the made assumptions.
    * @return The made assumptions or {@code null} if not available.
    * @throws Exception Occurred Exception.
    */
   public List<ProofMetaFileAssumption> checkAssumptions() throws Exception {
      if (metaFile != null && metaFile.exists()) {
         ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
         return pmfr.getAssumptions();
      }
      else {
         return null;
      }
   }

   /**
    * A modality.
    * @author Martin Hentschel
    */
   public static enum ContractModality {
      /**
       * Box modality.
       */
      BOX,
      
      /**
       * Diamond modality.
       */
      DIAMOND
   }
}
