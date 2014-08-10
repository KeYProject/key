package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.key_project.key4eclipse.resources.io.ProofMetaFileException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;

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
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProofStarter;

public class ProofRunnable implements Runnable {
   
   private IProject project;
   private List<ProofElement> proofElements;
   private List<ProofElement> proofsToDo;
   private final KeYEnvironment<CustomConsoleUserInterface> environment;
   private MarkerManager markerManager;
   private final IProgressMonitor monitor;
   
   public ProofRunnable(IProject project, List<ProofElement> proofElements, List<ProofElement> proofsToDo, KeYEnvironment<CustomConsoleUserInterface> environment, IProgressMonitor monitor){
      this.project = project;
      this.proofsToDo = proofsToDo;
      this.proofElements = proofElements;
      this.proofsToDo = proofsToDo;
      this.environment = environment;
      this.markerManager = new MarkerManager();
      this.monitor = monitor;
   }
   
   @Override
   public void run() {
      try{
         ProofElement pe;
         while ((pe = getProofToDo()) != null) {
            monitor.subTask("Building " + pe.getContract().getName());
         
            if(monitor.isCanceled()){
               monitor.worked(1);
            }
            else if(pe.getOverdueProofMarker() != null){
            
               pe.setKeYEnvironment(environment);
               pe.setProofObl(pe.getContract().createProofObl(environment.getInitConfig(), pe.getContract()));

               long proofStart = System.currentTimeMillis();
               Proof proof = processProof(pe);
               long proofDuration = System.currentTimeMillis()-proofStart;
               if(proof != null){
                  pe.setProofClosed(proof.closed());
                  pe.setProofReferences(ProofReferenceUtil.computeProofReferences(proof));
                  pe.setUsedContracts(KeYResourcesUtil.getUsedContractsProofElements(pe, proofElements));
                  pe.setMarkerMsg(generateProofMarkerMessage(pe, proof, proofDuration));
                  markerManager.setMarker(pe);
                  save(proof,pe);
                  markerManager.deleteOverdueProofMarker(pe);
                  proof.dispose();
               }
            }
            monitor.worked(1);
         }
         environment.dispose();
      } catch(Exception e){
         LogUtil.getLogger().logError(e);
      }
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
   private Proof processProof(ProofElement pe) throws Exception{
      IFile file = pe.getProofFile();
      Proof proof = null;
      if(!file.exists()){
         proof = createProof(pe);
      }
      else {
         proof = loadProof(pe);
         if(proof == null){
            proof = createProof(pe);
         }
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
      KeYEnvironment<CustomConsoleUserInterface> loadEnv = null;
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
      String newLine ="\n";
      
      sb.append(closed? "Closed Proof:" : "Open Proof:");
      sb.append(newLine);
      sb.append(pe.getContract().getName());
      sb.append(newLine);
      sb.append(newLine);
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
            sb.append(newLine);
            sb.append("Hint: Check code and specifications for bugs or continue proof interactively");
            sb.append(newLine);
            sb.append(newLine);
         }
         else{
            sb.append("Reason: Max. Rule Applications reached");
            sb.append(newLine);
            sb.append("Hint: Continue proof automatic- or interactively");
            sb.append(newLine);
            sb.append(newLine);
         }
      }
      
      sb.append("Time: " + time / 1000 + "." + time % 1000 + " s");
      sb.append(newLine);
      sb.append("Nodes: " + proof.countNodes());
      sb.append(newLine);
      sb.append("Branches: " + proof.countBranches());
      sb.append(newLine);
      
      return sb.toString();
   }
   
   private void save(Proof proof, ProofElement pe) throws CoreException, ProofMetaFileException {
      ByteArrayOutputStream out = generateSaveProof(proof, pe.getProofFile());
      IFile proofFile = pe.getProofFile();
      KeYProjectDelta keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
      keyDelta.addJobChangedFile(proofFile);
      saveProof(out, proofFile);
      keyDelta.addJobChangedFile(pe.getMetaFile());
      ProofMetaFileWriter pmfw = new ProofMetaFileWriter(pe);
      pmfw.writeMetaFile();
   }
   
   /**
    * Creates the {@link ByteOutputStream} for the given {@link Proof}.
    * @param proof - the {@link Proof} to use
    * @return the {@link ByteOutputStream} for the given {@link Proof}
    * @throws CoreException
    */
   private ByteArrayOutputStream generateSaveProof(Proof proof, IFile file) throws CoreException {
      Assert.isNotNull(proof);
      try {
         File location = ResourceUtil.getLocation(file);
         // Create proof file content
         ProofSaver saver = new ProofSaver(proof, location.getAbsolutePath(), Main.INTERNAL_VERSION);
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         String errorMessage = saver.save(out);
         if (errorMessage != null) {
            throw new CoreException(LogUtil.getLogger().createErrorStatus(errorMessage));
         }
         else {
            return out;
         }
      }
      catch (IOException e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e.getMessage(), e));
      }
   }
   
   /**
    * Saves the given {@link ByteOutputStream} into the proof{@link IFile} of the given {@link ProofElement}.
    * @param out - the {@link ByteArrayOutputStream} to use
    * @param pe - the {@link ProofElement} to use
    * @throws CoreException
    */
   private void saveProof(ByteArrayOutputStream out, IFile proofFile) throws CoreException{
      // Save proof file content
      createProofFolder(proofFile);
      if (proofFile.exists()) {
         proofFile.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
      }
      else {
         proofFile.create(new ByteArrayInputStream(out.toByteArray()), true, null);
      }
   }
   
   /**
    * Creates the proofFolder for the given proof{@link IFile}
    * @param proofFile - the proof{@link IFile} to use
    * @return the created {@link IFolder}
    * @throws CoreException
    */
   private IFolder createProofFolder(IFile proofFile) throws CoreException{
      IFolder proofFolder = null;
      IPath proofFolderPath = proofFile.getFullPath().removeLastSegments(1);
      IPath currentProofFolderPath = null;
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      for(int i = 0; i < proofFolderPath.segmentCount(); i++){
         if(currentProofFolderPath == null){
            currentProofFolderPath = new Path(proofFolderPath.segment(i));
         }
         else{
            currentProofFolderPath = currentProofFolderPath.append(proofFolderPath.segment(i));
            proofFolder = root.getFolder(currentProofFolderPath);
            if(!proofFolder.exists()){
               proofFolder.create(true, true, null);
            }
         }
         
      }
      return proofFolder;
   }
}
