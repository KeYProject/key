package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.marker.MarkerUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProofStarter;

public class ProofRunnable implements Runnable {
   
   private IProject project;
   private List<ProofElement> proofElements;
   private List<ProofElement> proofsToDo;
   private final KeYEnvironment<CustomUserInterface> environment;
   private final IProgressMonitor monitor;
   
   public ProofRunnable(IProject project, List<ProofElement> proofElements, List<ProofElement> proofsToDo, KeYEnvironment<CustomUserInterface> environment, IProgressMonitor monitor){
      this.project = project;
      this.proofsToDo = Collections.synchronizedList(proofsToDo);
      this.proofElements = proofElements;
      this.environment = environment;
      this.monitor = monitor;
   }
   
   @Override
   public void run() {
         ProofElement pe;
         while ((pe = getProofToDo()) != null) {
            monitor.subTask(pe.getContract().getName());

            if(monitor.isCanceled()){
               monitor.worked(1);
            }
            else if(pe.getBuild()){
            
               pe.setKeYEnvironment(environment);
               pe.setProofObl(pe.getContract().createProofObl(environment.getInitConfig(), pe.getContract()));

               long proofStart = System.currentTimeMillis();
               Proof proof = processProof(pe);
               long proofDuration = System.currentTimeMillis()-proofStart;
               if(proof != null){
                  pe.setProofClosed(proof.closed());
                  pe.setOutdated(false);
                  pe.setProofReferences(ProofReferenceUtil.computeProofReferences(proof));
                  pe.setUsedContracts(KeYResourcesUtil.getUsedContractsProofElements(pe, proofElements));
                  pe.setMarkerMsg(generateProofMarkerMessage(pe, proof, proofDuration));
                  try{
                     save(proof,pe);
                     MarkerUtil.setMarker(pe);
                  } catch (Exception e){
                     LogUtil.getLogger().logError(e);
                  }
                  proof.dispose();
               }
            }
            monitor.worked(1);
         }
         environment.dispose();
   }
   
   private ProofElement getProofToDo() {
      ProofElement pe = null;
      synchronized (proofsToDo) {
         if (!proofsToDo.isEmpty()) {
            pe = proofsToDo.remove(0);
         }
      }
      return pe;
   }
   
   
   /**
    * If the {@link ProofElement}s proof{@link IFile} exists the {@link Proof} stored in this {@link IFile} will be loaded. When the {@link Proof} is 
    * loaded and if it's not closed yet, the automode will be started. If the {@link IFile} doesn't exists a new Proof will be 
    * created and the automode will be started.
    * @param ProofElement - the {@link ProofElement} for the {@link Proof}
    * @throws Exception
    */
   private Proof processProof(ProofElement pe){
      IFile file = pe.getProofFile();
      Proof proof = null;
      try{
         if(!file.exists()){
            proof = createProof(pe);
         }
         else {
            proof = loadProof(pe);
            if(proof == null){
               proof = createProof(pe);
            }
         }
      } catch (ProofInputException e){
         LogUtil.getLogger().logError(e);
         return proof;
      }
      return proof;
   }
   
   
   /**
    * Creates a {@link Proof} for the given {@link ProofElement} and runs the AutoMode.
    * @param pe - the given {@link ProofElement}
    * @return the created {@link Proof}.
    * @throws ProofInputException 
    */
   private Proof createProof(ProofElement pe) throws ProofInputException{
         Proof proof = pe.getKeYEnvironment().createProof(pe.getProofObl());   
         
         StrategyProperties strategyProperties = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         strategyProperties.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);         
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(strategyProperties);
         
         ProofStarter ps = new ProofStarter(false);
         ps.init(new SingleProof(proof, pe.getProofObl().name()));
         ps.start();
         
         OneStepSimplifier oss = MiscTools.findOneStepSimplifier(proof);
         if (oss != null) {
            oss.refresh(proof);
         }
         return proof;
   }
   
   
   /**
    * Loads the {@link Proof} of the given {@link ProofElement} and runs the AutoMode.
    * @return the loaded {@link Proof}.}
    * @param ProofElement - the given {@link ProofElement}
    */
   private Proof loadProof(ProofElement pe){
      Proof proof = null;
      File file = pe.getProofFile().getLocation().toFile();
      Profile profile = pe.getKeYEnvironment().getInitConfig().getProfile();
      KeYEnvironment<CustomUserInterface> loadEnv = null;
      boolean error = false;
      try{
         loadEnv = KeYEnvironment.load(profile, file, null, null);
      } catch(ProblemLoaderException e){
         error = true;
      }
      if(loadEnv != null){
         proof = loadEnv.getLoadedProof();
         if (proof != null){
            if(error) {
               loadEnv.getUi().startAndWaitForAutoMode(proof);
            }
         }
      }
      return proof;
   }
   
   

   
   private String generateProofMarkerMessage(ProofElement pe, Proof proof, long time){
      StringBuffer sb = new StringBuffer();
      boolean closed = pe.getProofClosed();
      
      sb.append(closed? "Closed Proof:" : "Open Proof:");
      sb.append(StringUtil.NEW_LINE);
      sb.append(pe.getContract().getName());
      sb.append(StringUtil.NEW_LINE);
      sb.append(StringUtil.NEW_LINE);
      if(!proof.closed()){
         boolean uncloseable = false;
         OneStepSimplifier oss = MiscTools.findOneStepSimplifier(proof);
         if (oss != null) {
            oss.refresh(proof);
         }
         for(Goal goal : proof.openGoals()){
            
            if(!SymbolicExecutionUtil.hasApplicableRules(goal)){
               uncloseable = true;
               break;
            }
         }
         if(uncloseable){
            sb.append("Reason: Goal can't be closed automatically");
            sb.append(StringUtil.NEW_LINE);
            sb.append("Hint: Check code and specifications for bugs or continue proof interactively");
            sb.append(StringUtil.NEW_LINE);
            sb.append(StringUtil.NEW_LINE);
         }
         else{
            sb.append("Reason: Max. Rule Applications reached");
            sb.append(StringUtil.NEW_LINE);
            sb.append("Hint: Continue proof automatic- or interactively");
            sb.append(StringUtil.NEW_LINE);
            sb.append(StringUtil.NEW_LINE);
         }
      }
      
      sb.append("Time: " + time / 1000 + "." + time % 1000 + " s");
      sb.append(StringUtil.NEW_LINE);
      sb.append("Nodes: " + proof.countNodes());
      sb.append(StringUtil.NEW_LINE);
      sb.append("Branches: " + proof.countBranches());
      sb.append(StringUtil.NEW_LINE);
      
      return sb.toString();
   }
   
   private void save(Proof proof, ProofElement pe) throws Exception {
      ByteArrayOutputStream out = generateSaveProof(proof, pe.getProofFile());
      IFile proofFile = pe.getProofFile();
      KeYProjectDelta keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
      keyDelta.addJobChangedFile(proofFile);
      saveProof(out, proofFile, pe.getProofClosed());
      keyDelta.addJobChangedFile(pe.getMetaFile());
      ProofMetaFileWriter.writeMetaFile(pe);
   }
   
   /**
    * Creates the {@link ByteOutputStream} for the given {@link Proof}.
    * @param proof - the {@link Proof} to use
    * @return the {@link ByteOutputStream} for the given {@link Proof}
    * @throws CoreException
    */
   private ByteArrayOutputStream generateSaveProof(Proof proof, IFile file) {
      Assert.isNotNull(proof);
      try {
         File location = ResourceUtil.getLocation(file);
         // Create proof file content
         ProofSaver saver = new ProofSaver(proof, location.getAbsolutePath(), Main.INTERNAL_VERSION);
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         String errorMessage = saver.save(out);
         if (errorMessage != null) {
            return null;
         }
         return out;
      }
      catch (IOException e) {
         return null;
      }
   }
   
   /**
    * Saves the given {@link ByteOutputStream} into the proof{@link IFile} of the given {@link ProofElement}.
    * @param out - the {@link ByteArrayOutputStream} to use
    * @param pe - the {@link ProofElement} to use
    * @throws CoreException
    */
   private void saveProof(ByteArrayOutputStream out, IFile proofFile, boolean proofClosed) throws CoreException{
      // Save proof file content
      IFolder proofFolder = KeYResourcesUtil.createFolder(proofFile);
      if(proofFolder != null && proofFolder.exists()){
         if (proofFile.exists()) {
            proofFile.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
         }
         else {
            proofFile.create(new ByteArrayInputStream(out.toByteArray()), true, null);
         }
         KeYResourcesUtil.setProofClosed(proofFile, Boolean.valueOf(proofClosed));
      }
   }
}
