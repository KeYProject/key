package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.common.ui.testGeneration.EclipseTestGenerator;
import org.key_project.key4eclipse.resources.io.ProofMetaReferences;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.testgen.MemoryTestGenerationLog;
import de.uka.ilkd.key.smt.testgen.StopRequest;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * Runnable to perform the actual proof execution.
 * @author Stefan Käsdorf
 */
public class ProofRunnable implements Runnable {
   
   private IProject project;
   private List<ProofElement> proofElements;
   private List<ProofElement> proofsToDo;
   private final KeYEnvironment<DefaultUserInterfaceControl> environment;
   private final boolean generateTestCases;
   private final IProgressMonitor monitor;
   
   public ProofRunnable(IProject project, List<ProofElement> proofElements, List<ProofElement> proofsToDo, KeYEnvironment<DefaultUserInterfaceControl> environment, boolean generateTestCases, IProgressMonitor monitor){
      this.proofsToDo = Collections.synchronizedList(proofsToDo);
      this.project = project;
      this.proofElements = proofElements;
      this.environment = environment;
      this.generateTestCases = generateTestCases;
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
                  LinkedHashSet<IProofReference<?>> proofReferences = ProofReferenceUtil.computeProofReferences(proof);
                  Pair<List<IFile>, List<String>> usedElementsPair = KeYResourcesUtil.computeUsedProofElements(pe, proofReferences, proofElements);
                  pe.setUsedContracts(usedElementsPair.first);
                  pe.setCalledMethods(usedElementsPair.second);
                  pe.setMarkerMsg(generateProofMarkerMessage(pe, proof, proofDuration));
                  Set<IProofReference<?>> filteredProofReferences = new LinkedHashSet<IProofReference<?>>();
                  Set<IProofReference<?>> assumptions = new LinkedHashSet<IProofReference<?>>();
                  KeYResourcesUtil.filterProofReferences(proofReferences, filteredProofReferences, assumptions);
                  pe.setAssumptions(KeYResourcesUtil.computeProofMetaFileAssumtionList(pe.getKeYEnvironment().getServices(), assumptions));
                  pe.setProofMetaReferences(new ProofMetaReferences(pe, filteredProofReferences));
                  pe.setOutdated(false);
                  synchronized (ProofManager.proofsToSave) {
                     ProofManager.proofsToSave.add(new Pair<ProofElement, InputStream>(pe, generateSaveProof(proof, pe.getProofFile())));
                  }
                  if(generateTestCases && SolverType.Z3_CE_SOLVER.isInstalled(true)){
                     generateTestCases(pe, proof);
                  }
                  proof.dispose();
               }
            }
            monitor.worked(1);
         }
         environment.dispose();
   }

   private void generateTestCases(ProofElement pe, Proof proof){
      String packagename = KeYResourcesUtil.getJavaFilePackage(pe.getJavaFile());
      EclipseTestGenerator testGenerator = null;
      try {
         MemoryTestGenerationLog log = new MemoryTestGenerationLog();
         testGenerator = new EclipseTestGenerator(project, 
                                                  proof.name().toString(), 
                                                  packagename, 
                                                  environment.getUi(), 
                                                  proof, 
                                                  false);
         testGenerator.generateTestCases(new StopRequest() {
            @Override
            public boolean shouldStop() {
               return monitor.isCanceled();
            }
         }, log);
      }
      finally {
         if (testGenerator != null) {
            testGenerator.dispose();
         }
      }
   }


   /**
    * Acquires the next proof from the proof queue.
    * @return the next proof
    */
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
    * loaded and if it's not closed yet, the auto mode will be started. If the {@link IFile} doesn't exists a new Proof will be 
    * created and the auto mode will be started.
    * @param pe the {@link ProofElement} for the {@link Proof}
    * @return the created {@link Proof}
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
         ps.init(proof);
         ps.start();
         
         OneStepSimplifier.refreshOSS(proof);
         return proof;
   }
   
   
   /**
    * Loads the {@link Proof} of the given {@link ProofElement} and runs the AutoMode.
    * @return the loaded {@link Proof}.}
    * @param pe the given {@link ProofElement}
    */
   private Proof loadProof(ProofElement pe){
      Proof proof = null;
      File file = pe.getProofFile().getLocation().toFile();
      Profile profile = pe.getKeYEnvironment().getInitConfig().getProfile();
      KeYEnvironment<DefaultUserInterfaceControl> loadEnv = null;
      boolean error = false;
      try{
         loadEnv = KeYEnvironment.load(profile, file, null, null, null, false);
      } catch(ProblemLoaderException e){
         error = true;
      }
      if(loadEnv != null){
         proof = loadEnv.getLoadedProof();
         if (proof != null){
            if(error || loadEnv.getReplayResult().hasErrors()) {
               loadEnv.getProofControl().startAndWaitForAutoMode(proof);
            }
         }
      }
      return proof;
   }
   
   
   /**
    * Generates the message for the proof marker.
    * @param pe the {@link ProofElement} belonging to the {@link Proof}
    * @param proof the particular {@link Proof}
    * @param time the measured build time
    * @return the marker message
    */
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
         OneStepSimplifier.refreshOSS(proof);
         for(Goal goal : proof.openGoals()){
            
            if(!Goal.hasApplicableRules(goal)){
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
   
   /**
    * Creates the {@link ByteOutputStream} for the given {@link Proof}.
    * @param proof - the {@link Proof} to use
    * @param file the proofs proof{@link IFile}
    * @return the {@link ByteOutputStream} for the given {@link Proof}
    * @throws CoreException
    */
   private InputStream generateSaveProof(Proof proof, IFile file) {
      Assert.isNotNull(proof);
      try {
         final File location = ResourceUtil.getLocation(file);
         // Create proof file content
         OutputStreamProofSaver saver = new OutputStreamProofSaver(proof, KeYConstants.INTERNAL_VERSION) {
            @Override
            protected String getBasePath() throws IOException {
                return ProofSaver.computeBasePath(location);
            }
         };
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         saver.save(out);
         return new ByteArrayInputStream(out.toByteArray());
      }
      catch (IOException e) {
         return null;
      }
   }
}
