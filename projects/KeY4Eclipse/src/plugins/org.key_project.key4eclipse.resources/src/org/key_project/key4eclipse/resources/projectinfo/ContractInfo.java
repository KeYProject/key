package org.key_project.key4eclipse.resources.projectinfo;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
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
    * Constructor.
    * @param parent The parent {@link AbstractContractContainer} in which this {@link ContractInfo} is contained in.
    * @param name The name.
    * @param modality The optional modality.
    * @param proofFile The proof file.
    */
   public ContractInfo(AbstractContractContainer parent, String name, ContractModality modality, IFile proofFile) {
      Assert.isNotNull(parent);
      Assert.isNotNull(name);
      Assert.isNotNull(proofFile);
      this.name = name;
      this.parent = parent;
      this.modality = modality;
      this.proofFile = proofFile;
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
    * Checks if the object itself or one of its children has an open proof.
    * @return {@code true} open proof contained, {@code false} everything is successful proven or {@code null} if unknown.
    */
   public Boolean checkProofClosed() throws CoreException {
      return KeYResourcesUtil.isProofClosed(proofFile);
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
