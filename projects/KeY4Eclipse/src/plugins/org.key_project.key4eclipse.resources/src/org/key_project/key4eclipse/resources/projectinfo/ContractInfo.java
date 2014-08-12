package org.key_project.key4eclipse.resources.projectinfo;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileAssumption;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.gui.configuration.ChoiceSelector;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.KeYFile;

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
    * Checks if the proof depends on unproven dependencies.
    * @return A list of unproven dependencies or {@code null} if dependencies are not available because of a missing meta file.
    * @throws Exception Occurred Exception.
    */
   public List<IFile> checkUnprovenDependencies() throws Exception {
      if (metaFile != null && metaFile.exists()) {
         ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
         List<IFile> dependingProofs = pmfr.getUsedContracts();
         if (dependingProofs != null && !dependingProofs.isEmpty()) {
            List<IFile> unprovenProofs = new LinkedList<IFile>();
            for (IFile proofFile : dependingProofs) {
               Boolean closed = KeYResourcesUtil.isProofClosed(proofFile);
               if (closed == null || !closed.booleanValue()) {
                  unprovenProofs.add(proofFile);
               }
            }
            return unprovenProofs.isEmpty() ? null : unprovenProofs;
         }
         else {
            return null;
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
    * Checks the used taclet options for concerns about soundness and completeness.
    * @return The found issues or {@code null} if proof file does not exist.
    * @throws ProofInputException Occurred Exception
    */
   public TacletOptionIssues checkTaletOptions() throws ProofInputException {
      if (proofFile != null) {
         File localFile = ResourceUtil.getLocation(proofFile);
         if (localFile != null) {
            KeYFile file = new KeYFile("Check", localFile, null, AbstractProfile.getDefaultProfile());
            ProofSettings settings = file.readPreferences();
            List<String> unsoundTacletOptions = new LinkedList<String>();
            List<String> incompleteTacletOptions = new LinkedList<String>();
            List<String> informationTacletOptions = new LinkedList<String>();
            Map<String,String> choices = settings.getChoiceSettings().getDefaultChoices();
            for (String value : choices.values()) {
               if (ChoiceSelector.isUnsound(value)) {
                  unsoundTacletOptions.add(value);
               }
               if (ChoiceSelector.isIncomplete(value)) {
                  incompleteTacletOptions.add(value);
               }
               if (ChoiceSelector.getInformation(value) != null) {
                  informationTacletOptions.add(value);
               }
            }
            return new TacletOptionIssues(unsoundTacletOptions, incompleteTacletOptions, informationTacletOptions);
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * A summary of issues in taclet options computed by
    * {@link ContractInfo#checkTaletOptions()}.
    * @author Martin Hentschel
    */
   public static class TacletOptionIssues {
      /**
       * All used unsound taclet options.
       */
      private final List<String> unsoundOptions;
      
      /**
       * All used incomplete taclet options.
       */
      private final List<String> incompleteOptions;
      
      /**
       * All taclet options with some additional informations.
       */
      private final List<String> informationOptions;

      /**
       * Constructor.
       * @param unsoundOptions All used unsound taclet options.
       * @param incompleteOptions All used incomplete taclet options.
       * @param informationOptions All taclet options with some additional informations.
       */
      public TacletOptionIssues(List<String> unsoundOptions, List<String> incompleteOptions, List<String> informationOptions) {
         Assert.isNotNull(unsoundOptions);
         Assert.isNotNull(incompleteOptions);
         Assert.isNotNull(informationOptions);
         this.unsoundOptions = unsoundOptions;
         this.incompleteOptions = incompleteOptions;
         this.informationOptions = informationOptions;
      }

      /**
       * Returns all used unsound taclet options.
       * @return All used unsound taclet options.
       */
      public List<String> getUnsoundOptions() {
         return unsoundOptions;
      }

      /**
       * Returns all used incomplete taclet options.
       * @return All used incomplete taclet options.
       */
      public List<String> getIncompleteOptions() {
         return incompleteOptions;
      }

      /**
       * Returns all taclet options with some additional informations.
       * @return All taclet options with some additional informations.
       */
      public List<String> getInformationOptions() {
         return informationOptions;
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
