package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

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
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileTypeElement;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
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
   private List<IFile> changedJavaFiles;
   private List<ProofElement> proofElements;
   private List<ProofElement> proofsToDo;
   private final KeYEnvironment<CustomConsoleUserInterface> environment;
   private MarkerManager markerManager;
   private final IProgressMonitor monitor;
   
   public ProofRunnable(IProject project, List<IFile> changedJavaFiles, List<ProofElement> proofElements, List<ProofElement> proofsToDo, KeYEnvironment<CustomConsoleUserInterface> environment, IProgressMonitor monitor){
      this.project = project;
      this.proofsToDo = proofsToDo;
      this.changedJavaFiles = changedJavaFiles;
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
            pe.setKeYEnvironment(environment);
            pe.setProofObl(pe.getContract().createProofObl(environment.getInitConfig(), pe.getContract()));
            
            monitor.subTask("Building " + pe.getProofObl().name());
            
            boolean processProof = false;
            
            if(!KeYProjectProperties.isEnableBuildRequiredProofsOnly(project)){
               processProof = true;
            }
            else{
               IFile metaFile = pe.getMetaFile();
               if(pe.getMarker().isEmpty() || pe.getOverdueProofMarker() != null){
                  processProof = true;
               }
               else if(metaFile.exists()){
                  ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
                  LinkedList<IType> javaTypes = collectAllJavaITypes();
                  if(MD5changed(pe.getProofFile(), pmfr) || typeOrSubTypeChanged(pe, pmfr, javaTypes) || superTypeChanged(pe, javaTypes)){
                     processProof = true;
                  }
                  else{
                     pe.setProofClosed(pmfr.getProofClosed());
                     pe.setMarkerMsg(pmfr.getMarkerMessage());
                     pe.setUsedContracts(KeYResourcesUtil.getProofElementsByProofFiles(pmfr.getUsedContracts(), proofElements));
                  }
               }
               else{
                  processProof = true;
               }
            }
            
            if(processProof){
               if(monitor.isCanceled()){
                  markerManager.setOverdueProofMarker(pe);
               }
               else {
                  long proofStart = System.currentTimeMillis();
                  Proof proof = processProof(pe);
                  long proofDuration = System.currentTimeMillis()-proofStart;
                  if(proof != null){
                     pe.setProofClosed(proof.closed());
                     pe.setProofReferences(ProofReferenceUtil.computeProofReferences(proof));
                     pe.setUsedContracts(KeYResourcesUtil.getUsedContractsProofElements(pe, proofElements));
                     pe.setMarkerMsg(generateProofMarkerMessage(pe, proof, proofDuration));
                     markerManager.setMarker(pe);
                     markerManager.deleteOverdueProofMarker(pe);
                     save(proof,pe);
                     proof.dispose();
                  }
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
    * Collects all {@link IType}s of the project.
    * @return a {@link LinkedList} with all {@link IType}s
    * @throws JavaModelException
    */
   private LinkedList<IType> collectAllJavaITypes() throws JavaModelException{
      LinkedList<IType> typeList = new LinkedList<IType>();
      IJavaProject javaProject = JavaCore.create(project);
      IPackageFragment[] packageFragments = javaProject.getPackageFragments();
      for(IPackageFragment packageFragment : packageFragments){
         ICompilationUnit[] units = packageFragment.getCompilationUnits();
         for(ICompilationUnit unit : units){
            IType[] types = unit.getTypes();
            for(IType type : types){
               typeList.add(type);
               typeList.addAll(collectAllJavaITypesForIType(type));
            }
         }
      }
      return typeList;
   }
   
   /**
    * Collects all {@link IType}s of the gien {@link IType}.
    * @param type - the {@link IType} to use
    * @return all {@link IType}s of the given {@link IType}
    * @throws JavaModelException
    */
   private LinkedList<IType> collectAllJavaITypesForIType(IType type) throws JavaModelException{
      LinkedList<IType> types = new LinkedList<IType>();
      IType[] subTypes = type.getTypes();
      for(IType subType : subTypes){
         types.add(subType);
         types.addAll(collectAllJavaITypesForIType(subType));
      }
      return types;
   }
   
   /**
    * Checks if the MD5 of the proof{@link IFile} is different to the MD5 stored in the metafile.
    * @param proofFile - the proof{@link IFile} to use
    * @param pmfr - the {@link ProofMetaFileReader} to use
    * @return false if both MD5s are equal. true otherwise
    * @throws CoreException 
    * @throws IOException 
    */
   private boolean MD5changed(IFile proofFile, ProofMetaFileReader pmfr) throws IOException, CoreException{
      if(proofFile.exists()){
         String metaFilesProofMD5 = pmfr.getProofFileMD5();
         String proofFileHasCode = ResourceUtil.computeContentMD5(proofFile);
         if(metaFilesProofMD5.equals(proofFileHasCode)){
            return false;
         }
         else{
            return true;
         }
      }
      else{
         return true;
      }
   }
   
   /**
    * Checks if a type or a subtype from the metafile were changed.  
    * @param pmfr - the {@link ProofMetaFileReader} to use
    * @param javaTypes the {@link LinkedList} with all changed java{@link IFile}s
    * @return true if a type or a subtype was changed. false otherwise
    * @throws JavaModelException
    */
   private boolean typeOrSubTypeChanged(ProofElement pe, ProofMetaFileReader pmfr, LinkedList<IType> javaTypes) throws JavaModelException{
      LinkedList<ProofMetaFileTypeElement> typeElements = pmfr.getTypeElements();
      for(ProofMetaFileTypeElement te : typeElements){
         if(typeChanged(te.getType(), javaTypes)){
            return true;
         }
         else if(subTypeChanged(pe, te, javaTypes)){
            return true;
         }
      }
      return false;
   }
   
   /**
    * Checks if the given type was changed.
    * @param type - the type to check
    * @param javaTypes - all {@link IType}s of the project
    * @return true if the type was changed. false otherwise
    * @throws JavaModelException
    */
   private boolean typeChanged(String type, LinkedList<IType> javaTypes) throws JavaModelException{
      IFile javaFile = getJavaFileForType(type, javaTypes);
      //check if type has changed itself
      if(changedJavaFiles.contains(javaFile)){
         return true;
      }
      else {
         return false;
      }
   }
   
   /**
    * Chacks if any subTypes of the given {@link ProofMetaFileTypeElement} were changed.
    * @param te - the {@link ProofMetaFileTypeElement} to use
    * @param javaTypes - all {@link IType}s of the project
    * @return true if any subTypes were changed. false otherwise
    * @throws JavaModelException
    */
   private boolean subTypeChanged(ProofElement pe, ProofMetaFileTypeElement te, LinkedList<IType> javaTypes) throws JavaModelException{
      String type = te.getType();
      KeYJavaType kjt = getkeYJavaType(pe.getKeYEnvironment(), type);
//    ImmutableList<KeYJavaType> envSubKjts = environment.getJavaInfo().getAllSubtypes(kjt);
    ImmutableList<KeYJavaType> envSubKjts = pe.getKeYEnvironment().getJavaInfo().getAllSubtypes(kjt);
      
      LinkedList<String> subTypes = te.getSubTypes();
      
      if(envSubKjts.size() != subTypes.size()){
         return true;
      }
      else {
         for(String subType : subTypes){
            if(typeChanged(subType, javaTypes)){
               return true;
            }
         }
      }
      return false;
   }
   
   /**
    * Checks if any superTypes of the given {@link KeYJavaType} were changed.
    * @param kjt - the {@link KeYJavaType} to use
    * @param changedJavaFiles - all changed java{@link IFile}s
    * @param javaTypes - all {@link IType}s of the project
    * @return true if any superTypes were changed. false otherwise
    * @throws JavaModelException
    */
   private boolean superTypeChanged(ProofElement pe, LinkedList<IType> javaTypes) throws JavaModelException{
      KeYJavaType kjt = pe.getContract().getKJT();
      KeYJavaType envKjt = getkeYJavaType(pe.getKeYEnvironment(), kjt.getFullName());
      if(envKjt != null){
         ImmutableList<KeYJavaType> envSuperKjts = pe.getKeYEnvironment().getJavaInfo().getAllSupertypes(envKjt);
         for(KeYJavaType envSuperKjt : envSuperKjts){
            IFile javaFile = getJavaFileForType(envSuperKjt.getFullName(), javaTypes);
            if(changedJavaFiles.contains(javaFile)){
               return true;
            }
         }
         return false;
      }
      else{
         return true;
      }
   }
   
   /**
    * Returns the java{@link IFile} for the given metaType.
    * @param metaType - the given type
    * @param typeList - all {@link IType}s of the project
    * @return the java{@link IFile} for the given type
    * @throws JavaModelException
    */
   private IFile getJavaFileForType(String metaType, LinkedList<IType> typeList) throws JavaModelException{
      for(IType iType : typeList){
         String typeName = iType.getFullyQualifiedName('.');
         if(typeName.equalsIgnoreCase(metaType)){
            IPath filePath = iType.getResource().getFullPath();
            IFile javaFile = ResourcesPlugin.getWorkspace().getRoot().getFile(filePath);
            return javaFile;
         }
      }
      
      return null;
   }
   
   /**
    * Returns the {@link KeYJavaType} for the given fullName.
    * @param type - the types full name
    * @return the {@link KeYJavaType}
    */
   private KeYJavaType getkeYJavaType(KeYEnvironment<CustomConsoleUserInterface> env, String type){
      Set<KeYJavaType> envKjts = env.getServices().getJavaInfo().getAllKeYJavaTypes();
      for(KeYJavaType kjt : envKjts){
         if(type.equals(kjt.getFullName())){
            return kjt;
         }
      }
      return null;
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
//      proof = createProof(pe);
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
