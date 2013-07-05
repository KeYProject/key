/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import javax.xml.transform.TransformerException;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.swt.widgets.Display;
import org.key_project.key4eclipse.resources.io.ProofMetaFileContentException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileTypeElement;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.util.KeY4EclipseResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationInfo;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class ProofManager {

   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private MarkerManager markerManager;
   private IFolder mainProofFolder;
   private IProject project;   
   private List<Proof> proofs = new LinkedList<Proof>();
   private List<IFile> proofFiles;
   private IProgressMonitor monitor;
   
   /**
    * The Constructor - sets up the {@link MarkerManager}, the main Proof{@link IFolder} and tries 
    * to load the {@link KeYEnvironment}. If that fails the problemLoaderException will be set.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    * @throws ProblemLoaderException 
    */
   public ProofManager(IProject project) throws CoreException, ProblemLoaderException{
      markerManager = new MarkerManager();
      mainProofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(project.getFullPath().append("Proofs"));
      this.project = project;
      try {
         File location = ResourceUtil.getLocation(project);
         File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
         List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
         environment = KeYEnvironment.load(location, classPaths, bootClassPath);
         markerManager.deleteKeYMarker(project);
      }
      catch (ProblemLoaderException e) {
         handleProblemLoaderException(e);
         throw e;
      }
   }
   
   /**
    * Disposes this {@link ProofManager}.
    */
   public void dispose() {
//      if (environment != null) {
//         environment.dispose();
//      }
//      for (Proof proof : proofs) {
//         proof.dispose();
//      }
   }
   
   

   /**
    * Runs all {@link Proof}s available in the {@link IProject} and saves them into the proof{@link IFolder}.
    * @param autoDeleteProofFiles - enables or deletes the automatically proof{@link IFile} deletion
    * @throws Exception
    */
   public void runAllProofs(boolean autoDeleteProofFiles, IProgressMonitor mon) throws Exception{
      monitor = mon;
      LinkedList<ProofElement> proofElements = getAllProofElements();
      LinkedList<IFile> javaFiles = getAllJavaFilesFromProofElements(proofElements);
//      proofFiles = new LinkedList<IFile>();
      proofFiles = Collections.synchronizedList((LinkedList<IFile>)proofElements.clone());
      markerManager.deleteKeYMarker(javaFiles);
      markerManager.deleteKeYMarker(project);
      //set up monitor
      monitor.beginTask("Build all proofs", proofElements.size());
      init(proofElements);
//      runParallel(Integer.parseInt(project.getPersistentProperty(KeYProjectProperties.PROP_NUMBER_OF_THREADS)), proofElements, monitor);
//      for(ProofElement pe : proofElements){
//         monitor.subTask("Build " + pe.getProofObl().name());
//         IFolder proofFolder = createProofFolder(pe.getJavaFile());
//         IFile proofFile = getProofFile(pe.getProofObl().name(), proofFolder.getFullPath());
//         pe = processProof(pe, proofFile);
//         markerManager.setMarker(pe.getProof(), pe.getSourceLocation(), pe.getJavaFile(), proofFile);
//         if(pe.getProof() != null){
//            proofFiles.add(proofFile);
//            KeYUtil.saveProof(pe.getProof(), proofFile);
//            
//            IFile metaFile = saveMetaFile(proofFile, pe);
//            if(metaFile != null){
//               proofFiles.add(metaFile);
//            }
//            else{
//               //TODO: solve this problem
//               System.out.println("Warning: no meta file created for " + proofFile.getName());
//            }
//            pe.getProof().dispose();
//            pe.getKeYEnvironment().getMediator().setProof(null);
//         }
//         if(environment.getMediator().getSelectedProof() != null){
//            environment.getMediator().getSelectedProof().dispose();
//            environment.getMediator().getSelectionModel().setSelectedProof(null);
//         }
         monitor.worked(1);
//      }
      checkContractRecursion(proofElements);
      if(autoDeleteProofFiles){
         cleanProofFolder(proofFiles, mainProofFolder);
      }
      monitor.done();
   }


   public void runParallel(int threads, LinkedList<ProofElement> proofElements, IProgressMonitor monitor) throws InterruptedException{
      int numberThreadProofElements = proofElements.size() / threads;
      int modNumber = proofElements.size() % threads;
      int currentElementIndex = 0;         
      LinkedBlockingQueue<Runnable> runnables = new LinkedBlockingQueue<Runnable>();
      ThreadPoolExecutor tpe = new ThreadPoolExecutor(threads, threads, 1000, TimeUnit.SECONDS, runnables);
      for(int i = 0; i < threads; i++){
         LinkedList<ProofElement> threadProofElements = new LinkedList<ProofElement>();
         int toIndex = currentElementIndex + numberThreadProofElements;
         for(int j = currentElementIndex; j < toIndex; j++){
            threadProofElements.add(proofElements.get(j));
         }
         if(i < modNumber){
            threadProofElements.add(proofElements.get(toIndex));
            toIndex += 1;
         }
         currentElementIndex = toIndex;
         
         final LinkedList<ProofElement> finalProofElement = threadProofElements;
         Runnable runnable = new Runnable() {
            
            @Override
            public void run() {
               try{
                  synchronized (this) {
                     
                  
                  KeYEnvironment<CustomConsoleUserInterface> environment = cloneEnvironment();
                  for(ProofElement pe : finalProofElement){
   //                  monitor.subTask("Build " + pe.getProofObl().name());
                     IFolder proofFolder = createProofFolder(pe.getJavaFile());
                     IFile proofFile = getProofFile(pe.getProofObl().name(), proofFolder.getFullPath());
                     pe = processProof(pe, proofFile);
                     markerManager.setMarker(pe.getProof(), pe.getSourceLocation(), pe.getJavaFile(), proofFile);
                     if(pe.getProof() != null){
                        proofFiles.add(proofFile);
                        KeYUtil.saveProof(pe.getProof(), proofFile);
                        
                        IFile metaFile = saveMetaFile(proofFile, pe);
                        if(metaFile != null){
                           proofFiles.add(metaFile);
                        }
                        else{
                           //TODO: solve this problem
                           System.out.println("Warning: no meta file created for " + proofFile.getName());
                        }
                     }
                     if(environment.getMediator().getSelectedProof() != null){
                        environment.getMediator().getSelectedProof().dispose();
                        environment.getMediator().getSelectionModel().setSelectedProof(null);
                     }
   //                  monitor.worked(1);
                  }
               }}
               catch (Exception e) {
                  LogUtil.getLogger().createErrorStatus(e);
               }
            }    
         };
         tpe.execute(runnable);
      }
   }
   
   
   private boolean sameHashCode(IFile proofFile, ProofMetaFileReader pmfr) throws Exception{
      if(proofFile.exists()){
         int metaFilesProofHashCode = pmfr.getProofFileHashCode();
         int proofFileHasCode = proofFile.hashCode();
         if(proofFileHasCode == metaFilesProofHashCode){
            return true;
         }
         else{
            return false;
         }
      }
      else{
         return false;
      }
   }
   
   
   private boolean typeChanged(ProofMetaFileReader pmfr, LinkedList<IFile> changedJavaFiles) throws Exception{
      LinkedList<IType> javaTypes = collectAllJavaITypes();
      LinkedList<ProofMetaFileTypeElement> typeElements = pmfr.getTypeElements();
      for(ProofMetaFileTypeElement te : typeElements){
         String type = te.getType();
         IFile javaFile = getJavaFileForType(type, javaTypes);
         //check if type has changed itself
         if(changedJavaFiles.contains(javaFile)){
            return true;
         }
      }
      return false;
   }
  
   
   private boolean subTypesChanged(ProofMetaFileReader pmfr) throws ProofMetaFileContentException{
      LinkedList<ProofMetaFileTypeElement> typeElements = pmfr.getTypeElements();
      for(ProofMetaFileTypeElement te : typeElements){
         LinkedList<String> subTypes = te.getSubTypes();
         Set<KeYJavaType> envKjts = environment.getServices().getJavaInfo().getAllKeYJavaTypes();
         KeYJavaType equiKjt = null;
         for(KeYJavaType kjt : envKjts){
            if(te.getType().equals(kjt.getFullName())){
               equiKjt = kjt;
            }
         }
         if(equiKjt == null){
            return true;
         }
         else{
            ImmutableList<KeYJavaType> envSubTypes = environment.getServices().getJavaInfo().getAllSubtypes(equiKjt);
            for(KeYJavaType kjt: envSubTypes){
               System.out.println(kjt.getFullName());
            }
            if(envSubTypes.size() == subTypes.size()){
               for(KeYJavaType envSubType : envSubTypes){
                  String envSubTypeName = envSubType.getFullName();
                  if(!subTypes.contains(envSubTypeName)){
                     return true;
                  }
               }
            }
            else{
               return true;
            }
         }
      }
      return false;
   }
   
   
   private ProofElement runProof(ProofElement pe, IFile proofFile) throws Exception{
      System.out.println(pe.getProofObl().name());
      markerManager.deleteMarkerForSourceLocation(pe.getJavaFile(), pe.getSourceLocation());
      pe = processProof(pe, proofFile);
      markerManager.setMarker(pe.getProof(), pe.getSourceLocation(), pe.getJavaFile(), proofFile);
      if(pe.getProof() != null){
         KeYUtil.saveProof(pe.getProof(), proofFile);
         IFile metaFile = saveMetaFile(proofFile, pe);
         if(metaFile == null){
            System.out.println("Warning: no meta file created for " + proofFile.getName());
         }
      }
      return pe;
   }

   
   public void runProofsSelective(LinkedList<IFile> changedJavaFiles, boolean autoDeleteProofFiles, IProgressMonitor monitor) throws Exception{
      LinkedList<IFile> proofFiles = new LinkedList<IFile>();
      LinkedList<ProofElement> proofElements = getAllProofElements();
      monitor.beginTask("Build all proofs", proofElements.size());
      for(ProofElement pe : proofElements){
         monitor.subTask("Build " + pe.getProofObl().name());
         //check if Proof exists
         IFolder proofFolder = createProofFolder(pe.getJavaFile());
         IFile proofFile = getProofFile(pe.getProofObl().name(), proofFolder.getFullPath());
         IFile metaFile = getProofMetaFile(proofFile);
         if(metaFile.exists()){
            ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
            if(sameHashCode(proofFile, pmfr)){
               if(typeChanged(pmfr, changedJavaFiles)){
                runProof(pe, proofFile);
               }
               else{
                  if(subTypesChanged(pmfr)){
                     pe = runProof(pe, proofFile);
                  }
               }
            }
            else{
               runProof(pe, proofFile);
            }
         }
         else{
            runProof(pe, proofFile);
         }
         
         if(autoDeleteProofFiles){
            proofFiles.add(proofFile);
            proofFiles.add(metaFile);
         }
         if(environment.getMediator().getSelectedProof() != null){
            environment.getMediator().getSelectedProof().dispose();
            environment.getMediator().getSelectionModel().setSelectedProof(null);
         }
         monitor.worked(1);
      }
      
      checkContractRecursion(proofElements);
      
      if(autoDeleteProofFiles){
         cleanProofFolder(proofFiles, mainProofFolder);  
      }
      monitor.done();
   }
   
   
   private void checkContractRecursion(LinkedList<ProofElement> proofElements) throws CoreException{
      RecursionGraph graph = new RecursionGraph(proofElements);
      LinkedHashSet<ProofElement> cyclingElements = graph.findCycles();
      for(ProofElement pe : cyclingElements){
         markerManager.deleteMarkerForSourceLocation(pe.getJavaFile(), pe.getSourceLocation());
         markerManager.setCycleDetectedMarker(pe);
      }
   }
   
   
   
   /**
    * Collects all {@link Proof}s available in the {@link IProject} and returns their
    * {@link ProofOblInput}s, java{@link IFiles}s and {@link SourceLocation}s as 
    * {@link ProofElement}s in a {@link LinkedList}.
    * @return - the {@link LinkedList} with all {@link ProofElement}s
    * @throws CoreException 
    */
   private LinkedList<ProofElement> getAllProofElements() throws CoreException {
      Set<KeYJavaType> kjts = environment.getJavaInfo().getAllKeYJavaTypes();
      KeYJavaType[] kjtsarr = KeY4EclipseResourcesUtil.sortKeYJavaTypes(kjts);
      LinkedList<ProofElement> proofElements = new LinkedList<ProofElement>();
      for (KeYJavaType type : kjtsarr) {
         ImmutableSet<IObserverFunction> targets = environment.getSpecificationRepository().getContractTargets(type);
         Type javaType = type.getJavaType();
         IFile javaFile = null;
         SourceLocation scl = null;
         if(javaType instanceof JavaSourceElement){
            JavaSourceElement javaElement = (JavaSourceElement) javaType;
            String fileName = SymbolicExecutionUtil.getSourcePath(javaElement.getPositionInfo());
            IPath location = new Path(fileName);
            IPath relatviePath = location.makeRelativeTo(project.getLocation().removeLastSegments(1));
            javaFile = ResourcesPlugin.getWorkspace().getRoot().getFile(relatviePath);
            scl = KeYUtil.convertToSourceLocation(javaElement.getPositionInfo());
         }
         for (IObserverFunction target : targets) {
            if(target instanceof IProgramMethod){
               IProgramMethod progMethod = (IProgramMethod) target;
               if(progMethod.getContainerType().getJavaType().equals(javaType)){
                  scl = KeYUtil.convertToSourceLocation(progMethod.getPositionInfo());
               }
            }
            ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getContracts(type, target);
            for (Contract contract : contracts) {
               ProofOblInput obl = contract.createProofObl(environment.getInitConfig(), contract);
               IFolder proofFolder = createProofFolder(javaFile);
               IFile proofFile = getProofFile(obl.name(), proofFolder.getFullPath());
               proofElements.add(new ProofElement(obl, javaFile, scl, proofFolder, proofFile, type, environment, contract));
            }
         }
      }
      return proofElements;
   }
   
   
   private KeYEnvironment<CustomConsoleUserInterface> cloneEnvironment(){
      System.out.println("Cloning");

            InitConfig sourceInitConfig = environment.getInitConfig();
            RuleJustificationInfo sourceJustiInfo = environment.getInitConfig().getProofEnv().getJustifInfo();
            // Create new profile which has separate OneStepSimplifier instance
            JavaProfile profile = new JavaProfile() {
               private OneStepSimplifier simplifier;
               
               @Override
               protected OneStepSimplifier getInitialOneStepSimpilifier() {
                  if (simplifier == null) {
                     simplifier = new OneStepSimplifier();
                  }
                  return simplifier;
               }
            };
            // Create new InitConfig and initialize it with value from initial one.
            InitConfig initConfig = new InitConfig(environment.getServices().copy(), environment.getProfile());
            initConfig.setActivatedChoices(sourceInitConfig.getActivatedChoices());
            initConfig.setSettings(sourceInitConfig.getSettings());
            initConfig.setTaclet2Builder(sourceInitConfig.getTaclet2Builder());
            initConfig.setTaclets(sourceInitConfig.getTaclets());
            // Create new ProofEnvironment and initialize it with values from initial one.
            ProofEnvironment env = initConfig.getProofEnv();
            env.setJavaModel(sourceInitConfig.getProofEnv().getJavaModel());
            env.setRuleConfig(sourceInitConfig.getProofEnv().getRuleConfig());
            for (Taclet taclet : sourceInitConfig.activatedTaclets()) {
               env.getJustifInfo().addJustification(taclet, sourceInitConfig.getProofEnv().getJustifInfo().getJustification(taclet));
            }
            for (BuiltInRule rule : initConfig.builtInRules()) {
               RuleJustification origJusti = sourceInitConfig.getProofEnv().getJustifInfo().getJustification(rule);
               if (origJusti == null) {
                  assert rule instanceof OneStepSimplifier;
                  origJusti = AxiomJustification.INSTANCE;
               }
               env.getJustifInfo().addJustification(rule, origJusti);
            }
//            GlobalProofMgt.getInstance().registerProofEnvironment(env);
            KeYEnvironment<CustomConsoleUserInterface> keyEnv = new KeYEnvironment<CustomConsoleUserInterface>(new CustomConsoleUserInterface(false), initConfig);
            return environment;
         }
   
   
   /**
    * Collects all java{@link IFile}s from the given {@link ProofElement}s.
    * @param proofElements - the given {@link ProofElement}s
    * @return - the {@link LinkedList} with all java{@link IFile}s
    */
   private LinkedList<IFile> getAllJavaFilesFromProofElements(LinkedList<ProofElement> proofElements) {
      LinkedList<IFile> javaFiles = new LinkedList<IFile>();
      for(ProofElement pe : proofElements){
         IFile javaFile = pe.getJavaFile();
         if(!javaFiles.contains(javaFile)){
            javaFiles.add(javaFile);
         }
      }
      return javaFiles;
   }
   
   
   /**
    * Deletes the main Proof{@link IFolder} and runs all {@link Proof}s for the {@link IProject}.
    * @throws Exception
    */
   public void clean(boolean autoDeleteProofFiles, IProgressMonitor monitor) throws Exception{
      deleteResource(mainProofFolder);
      runAllProofs(autoDeleteProofFiles, monitor);
   }
   
   
   /**
    * Cleans every {@link IFolder} in the MainProofFolder by removing all files which are not 
    * listed in the given {@link LinkedList}. Empty {@link IFolder} will be deleted.
    * @param proofFiles - the {@link LinkedList} to use
    * @param folder - the {@link IFolder} to start at
    * @throws CoreException
    */
   private void cleanProofFolder(List<IFile> proofFiles, IFolder folder) throws CoreException{
      IResource[] members = folder.members();
      for(IResource res : members){
         if(res.getType() == IResource.FILE){
            if(!proofFiles.contains(res)){
               res.delete(true, null);
            }
         }
         else if(res.getType() == IResource.FOLDER){
            cleanProofFolder(proofFiles, (IFolder) res);
         }
      }
      if(folder.members().length == 0){
         folder.delete(true, null);
      }
   }
   
   
   /**
    * Deletes the given {@link IResource} and every empty {@link IFolder} above.
    * @param res - the {@link IResource} to be deleted
    * @throws CoreException
    */
   public void deleteResource(IResource res) throws CoreException{
      if(res != null){
         IContainer container = res.getParent();
         res.delete(true, null);
         if(container.getType() == IResource.FOLDER){
            IFolder folder = (IFolder) container;
            deleteUnnecessaryFolders(folder);
         }
      }
   }
   
   
   /**
    * Deletes every {@link IFolder} with no members including and above the given {@link IFolder}.
    * @param folder - the given {@link IFolder}
    * @throws CoreException
    */
   private void deleteUnnecessaryFolders(IFolder folder) throws CoreException{
      if(folder.members().length == 0){
         IContainer container = folder.getParent();
         folder.delete(true, null);
         if(container.getType() == IResource.FOLDER){
            IFolder parentFolder = (IFolder) container;
            deleteUnnecessaryFolders(parentFolder);
         }
      }
   }
   
   
   /**
    * Creates the proofFolderStructure for the given {@link IResource} which must be a javaFile.
    * @param res - the given {@link IResource}
    * @return the created {@link IFolder}
    * @throws CoreException
    */
   private IFolder createProofFolder(IResource res) throws CoreException{
      IFolder proofFolder = mainProofFolder;
      if(!proofFolder.exists()){
         proofFolder.create(true, true, null);
      }
      IPath proofPath = javaToProofPath(res.getFullPath());
      IPath currentProofFolderPath = mainProofFolder.getFullPath();
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      for(String folderName : proofPath.segments()){
         currentProofFolderPath = currentProofFolderPath.append(folderName);
          proofFolder = root.getFolder(currentProofFolderPath);
         if(!proofFolder.exists()){
            proofFolder.create(true, true, null);
         }
      }
      return proofFolder;
   }
   
   
   /**
    * If the given {@link IFile} exists the {@link Proof} stored in this {@link IFile} will be loaded. When the {@link Proof} is 
    * loaded and if it's not closed yet, the automode will be started. If the {@link IFile} doesn't exists a new Proof will be 
    * created and the automode will be started.
    * @param obl - the {@link ProofOblInput} for the {@link Proof}
    * @param file - the {@link IFile} of the {@link Proof}
    * @return - the created {@link Proof}
    * @throws Exception
    */
   private ProofElement processProof(ProofElement pe, IFile file) throws Exception{      
      if(!file.exists()){
         pe = createProof(pe);
      }
      else{
         File proofFile = file.getLocation().toFile();
         pe = loadProof(pe, proofFile);
         if(pe.getProof() == null){
            pe = createProof(pe);
         }
      }
      return pe;  
   }
   
   
   /**
    * Creates a {@link Proof} for the given {@link ProofOblInput} and runs the AutoMode.
    * @param obl - the given {@link ProofOblInput}
    * @return the created {@link Proof}
    */
   private ProofElement createProof(ProofElement pe){
      try{
         Proof proof = pe.getKeYEnvironment().createProof(pe.getProofObl());
         proofs.add(proof);
         pe.getKeYEnvironment().getMediator().setProof(proof);
         pe.getKeYEnvironment().getUi().startAndWaitForAutoMode(proof);
         pe.setProof(proof);
         pe.setProofReferences(ProofReferenceUtil.computeProofReferences(proof));
         return pe;
      }catch(ProofInputException e){
         LogUtil.getLogger().createErrorStatus(e);
         return null;
      }
   }
   
   
   /**
    * Loads the {@link Proof} of the given {@link IFile} and runs the AutoMode.
    * @param file - the given {@link IFile}
    * @return the loaded {@link Proof}
    */
   private ProofElement loadProof(ProofElement pe, File file){
      try{
         KeYEnvironment<CustomConsoleUserInterface> loadEnv = KeYEnvironment.load(file, null, null);
         Proof proof = loadEnv.getLoadedProof();
         pe.setKeYEnvironment(loadEnv);
         pe.setProof(proof);
         pe.setProofReferences(ProofReferenceUtil.computeProofReferences(proof));
         if (proof != null) {
            proofs.add(proof);
            if (!proof.closed()){
               environment.getUi().startAndWaitForAutoMode(proof);
            }
         }
         return pe;
      }catch(Exception e){
         LogUtil.getLogger().createErrorStatus(e);
         return createProof(pe);
      }
   }
   
   
   /**
    * Returns the Proof-{@link IFile} for the given {@link String} and {@link IPath}.
    * @param name - the name for the {@link IFile}
    * @param path - the {@link IPath} for the {@link IFile} 
    * @return - the {@link IFile} for the Proof
    */
   private IFile getProofFile(String name, IPath path){
      if(path != null && name != null){
         name = makePathValid(name);
         name = name + ".proof";
         path = path.append(name);
         IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
         return file;
      }
      else return null;
   }
   
   
   private IFile getProofMetaFile(IFile proofFile){
      IPath proofFilePath = proofFile.getFullPath();
      IPath proofMetaFilePath = proofFilePath.addFileExtension("meta");
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile proofMetaFile = root.getFile(proofMetaFilePath);
      return proofMetaFile;
   }
   
   
   /**
    * Replaces invalid characters in the given {@link String} with '_' and returns a valid {@link String}.
    * @param str - the {@link String} to be made valid.
    * @return the valid {@link String}
    */
   private String makePathValid(String str){

      String tmp;
      for(int i = 1; i<=str.length();i++){
         tmp = str.substring(0, i);
         IStatus validStatus = ResourcesPlugin.getWorkspace().validateName(tmp, IResource.FILE);
         if(!validStatus.isOK()){
            StringBuilder strbuilder = new StringBuilder(str);
            strbuilder.setCharAt(i-1, '_');
            str = strbuilder.toString();
         }
      }
      return str;
   }
   
   
   /**
    * Returns the Java-{@link IResource} for the given Proof-{@link IResource}
    * @param res - the given Proof-{@link IResource}
    * @return the Java-{@link IFile}
    */
   public IFile getJavaFileForProofFile(IResource res){
      IContainer container = res.getParent();
      if(container.getType() == IResource.FOLDER){
         IFolder folder = (IFolder) container;
         IPath path = proofToJavaPath(folder.getFullPath());
         IPath javaPath = res.getProject().getFullPath().append("src").append(path);
         IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
         IFile javaFile = root.getFile(javaPath);
         if(javaFile.exists()){
            return javaFile;
         }
      }
      return null;
   }
   
   
   /**
    * Converts a javaFiles {@link IPath} to a proofFolder {@link Path}.
    * @param path - the JavaFile {@link IPath}.
    * @return
    */
   private IPath javaToProofPath(IPath path){
      while(path.segmentCount() > 0){
         if(!path.segment(0).equals("src")){
            path = path.removeFirstSegments(1);
         }
         else{
            path = path.removeFirstSegments(1);
            break;
         }
      }
      return path;
   }
   
   
   /**
    * Converts a proofFolders {@link IPath} to a sourceFolder {@link IPath}.
    * @param path the given proofFolder {@link IPath}
    * @return the sourceFolder {@link IPath} for the given proofFolder {@link IPath}
    */
   private IPath proofToJavaPath(IPath path){
      while(path.segmentCount() > 0){
         if(!path.segment(0).equals("Proofs")){
            path = path.removeFirstSegments(1);
         }
         else{
            path = path.removeFirstSegments(1);
            break;
         }
      }
      return path;
   }
   
   
   /**
    * Collects all Java{@link IFile}s of the {@link IProject}.
    * @return the {@link LinkedList} with all Java{@link IFile}s
    * @throws JavaModelException
    */
   private LinkedList<IFile> collectAllJavaFilesForProject() throws JavaModelException{
      IJavaProject javaProject = JavaCore.create(project);
      LinkedList<IFile> javaFiles = new LinkedList<IFile>();
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath sourcePath = project.getFullPath().append("src");
      IPackageFragment[] packageFragments = javaProject.getPackageFragments();
      for(IPackageFragment packageFragment : packageFragments){
         ICompilationUnit[] units = packageFragment.getCompilationUnits();
         for(ICompilationUnit unit : units){            
            IPath filePath = unit.getResource().getFullPath();
            IFile javaFile = root.getFile(unit.getResource().getFullPath());
            if(!javaFiles.contains(javaFile) && sourcePath.isPrefixOf(filePath)){
               javaFiles.add(javaFile);
            }
         }
      }
      return javaFiles;
   }
   
   
   /**
    * Handles the occurrence of a {@link ProblemLoaderException}. All KeYMarker will be deleted and a ProblemException{@link IMarker} will be set.
    * @param e - the {@link ProblemLoaderException}
    * @throws CoreException
    */
   private void handleProblemLoaderException(ProblemLoaderException e) throws CoreException{
      //remove all KeYMarker in the whole project
      markerManager.deleteKeYMarker(project);
      LinkedList<IFile> allFiles = collectAllJavaFilesForProject();
      for(IFile file : allFiles){
         markerManager.deleteKeYMarker(file);
      }
      //add the ProblemExceptionMarker
      markerManager.setProblemLoaderExceptionMarker(project, e.getMessage());
   }
   
   
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
   
   
   private LinkedList<IType> collectAllJavaITypesForIType(IType type) throws JavaModelException{
      LinkedList<IType> types = new LinkedList<IType>();
      IType[] subTypes = type.getTypes();
      for(IType subType : subTypes){
         types.add(subType);
         types.addAll(collectAllJavaITypesForIType(subType));
      }
      return types;
   }
   
   
   private IFile saveMetaFile(IFile proofFile, ProofElement pe) throws  TransformerException, CoreException{
      ProofMetaFileWriter metaFileWriter = new ProofMetaFileWriter();
      return metaFileWriter.writeMetaFile(proofFile, pe);
   }


   private List<ProofElement> proofsToDo = Collections.synchronizedList(new LinkedList<ProofElement>());
   
   protected ProofElement getProofToDo() {
      ProofElement pe = null;
      synchronized (proofsToDo) {
         if (!proofsToDo.isEmpty()) {
            pe = proofsToDo.remove(0);
            // TODO: Update progress monitor
            monitor.worked(1);
         }
      }
      return pe;
   }
   
   
   private List<ProofElement> proofsToSave = Collections.synchronizedList(new LinkedList<ProofElement>());
   
   protected void saveProofFormList(){
      
   }
   
   public void init(LinkedList<ProofElement> proofElements) {
      proofsToDo = Collections.synchronizedList((LinkedList<ProofElement>)proofElements.clone());
      // Fill proofsToDO;
      int numOfThreads = 2;
      if (numOfThreads >= 2) {
         Thread[] threads = new Thread[numOfThreads];
         for (int i = 0; i < numOfThreads; i++) {
            // TODO: Each thread needs a clone of the environment
            ProofRunnable run = new ProofRunnable(cloneEnvironment());
            Thread thread = new Thread(run);
            thread.start();
            threads[i] = thread;
         }
         ObjectUtil.waitForThreads(threads);
         // Wait until all threads have terminated
         while(!proofsToSave.isEmpty()){
            ProofElement pe = proofsToSave.remove(0);
            try {
               KeYUtil.saveProof(pe.getProof(), pe.getProofFile());
            }
            catch (CoreException e) {
               e.printStackTrace();
            }
         }
         
      }
      else {
         ProofRunnable run = new ProofRunnable(cloneEnvironment());
         run.run();
      }
      // Set marker
      System.out.println("Done");
   }
   
   private List<ProofElement> peToSave = Collections.synchronizedList(new LinkedList<ProofElement>());
   
   protected void saveProoff(final ProofElement pe){
      System.out.println("save " + Thread.currentThread().getName());
   }

   private class ProofRunnable implements Runnable {
      
      private KeYEnvironment<CustomConsoleUserInterface> environment;
      
      public ProofRunnable(KeYEnvironment<CustomConsoleUserInterface> environment){
         this.environment = environment;
      }
      
      @Override
      public void run() {
         ProofElement pe;
         while ((pe = getProofToDo()) != null) {
              // Work with proof
         try{
               pe.setKeYEnvironment(environment);
               IFolder proofFolder = pe.getProofFolder();
               IFile proofFile = getProofFile(pe.getProofObl().name(), proofFolder.getFullPath());
               pe = processProof(pe, proofFile);
               markerManager.setMarker(pe.getProof(), pe.getSourceLocation(), pe.getJavaFile(), proofFile);
               if(pe.getProof() != null){
                  proofFiles.add(proofFile);
                  proofsToSave.add(pe);
                  //diesen thread warten lassen
                  //speichern
                  //thread weiter laufen lassen
                  
//                  KeYUtil.saveProof(pe.getProof(), proofFile);                     
//                  IFile metaFile = saveMetaFile(proofFile, pe);
//                  if(metaFile != null){
//                     proofFiles.add(metaFile);
//                  }
//                  else{
//                     //TODO: solve this problem
//                     System.out.println("Warning: no meta file created for " + proofFile.getName());
//                  }
                  pe.getProof().dispose();
                  pe.getKeYEnvironment().getMediator().setProof(null);
               }
            }catch(Exception e){
                e.printStackTrace();
            }
         }
      }
   }
}
