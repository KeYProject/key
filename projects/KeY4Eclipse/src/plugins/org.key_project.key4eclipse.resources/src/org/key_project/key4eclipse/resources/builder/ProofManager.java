/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.EditorSelection;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * The ProofManager is responsible for the maintasks during the build. It runs and saves the 
 * proofs, creates marker, initializes threads and manages the folderstructure.
 * @author Stefan Käsdorf
 */
public class ProofManager {

   private final IProject project;
   private int buildType;
   private final IFolder mainProofFolder;
   private List<ProofElement> proofElements;
   private List<IFile> changedJavaFiles;
   private List<Object> outdatedCheckElements;
   private EditorSelection editorSelection;
   private final MarkerManager markerManager;
   private final KeYEnvironment<CustomUserInterface> environment;
   private List<ProofElement> proofQueue = Collections.synchronizedList(new LinkedList<ProofElement>());

   
   /**
    * The Constructor that loads the {@link KeYEnvironment}. If that fails the problemLoaderException will be set.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    * @throws ProblemLoaderException 
    */
   public ProofManager(IProject project, int buildType, List<Object> outdatedCheckElements, EditorSelection editorSelection) throws CoreException, ProblemLoaderException{
      this.project = project;
      this.buildType = buildType;
      this.mainProofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME));
      KeYProjectDelta keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
      this.changedJavaFiles = keyDelta.getChangedJavaFiles();
      keyDelta.reset();
      this.outdatedCheckElements = outdatedCheckElements;
      this.editorSelection = editorSelection;
      this.markerManager = new MarkerManager();markerManager.deleteKeYMarkerByType(project, IResource.DEPTH_ZERO, MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID);     
      try {
         File location = KeYUtil.getSourceLocation(project);
         File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
         List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
         environment = KeYEnvironment.load(location, classPaths, bootClassPath);
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
      if (environment != null) {
         environment.dispose();
      }
   }
   
   
   /**
    * Handles the occurrence of a {@link ProblemLoaderException}. All KeYMarker will be deleted and a ProblemException{@link IMarker} will be set.
    * @param e - the {@link ProblemLoaderException}
    * @throws CoreException
    */
   private void handleProblemLoaderException(ProblemLoaderException e) throws CoreException{
      //remove all KeYMarker in the whole project
      markerManager.deleteAllKeYMarker(project, IResource.DEPTH_INFINITE);
      //add the ProblemExceptionMarker
      markerManager.setProblemLoaderExceptionMarker(project, e.getMessage());
   }
   

   /**
    * Runs the {@link Proof}s available in the {@link IProject} dependent on the ProofManageMentProperties.
    * @param changedJavaFiles - {@link LinkedList} with all changed java{@link IFile}s
    * @param monitor - the {@link IProgressMonitor}
    * @throws Exception
    */
   public void runProofs(IProgressMonitor monitor) throws CoreException{
      proofElements = getAllProofElements();
      setProofElementsOutdated();
      sortProofElements(editorSelection);
      cleanMarker();
      if(KeYProjectProperties.isAutoDeleteProofFiles(project)){
         cleanProofFolder(getAllFiles(), mainProofFolder);
      }
      //set up monitor
      monitor.beginTask("Building proofs for " + project.getName(), proofElements.size());
      initThreads(monitor);
      checkContractRecursion();
      monitor.done();
   }
   
   
   /**
    * Collects all {@link Proof}s available in the {@link IProject} and returns their
    * java{@link IFiles}, {@link SourceLocation}, {@link IMarker}, proof{@link IFolder} and {@link Contract} as 
    * {@link ProofElement}s in a {@link LinkedList}.
    * @return - the {@link LinkedList} with all {@link ProofElement}s
    * @throws CoreException 
    */
   private LinkedList<ProofElement> getAllProofElements() throws CoreException {
      Set<KeYJavaType> kjts = environment.getJavaInfo().getAllKeYJavaTypes();
      KeYJavaType[] kjtsarr = KeYUtil.sortKeYJavaTypes(kjts);
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
            scl = KeYUtil.updateToMethodNameLocation(javaFile, scl);
         }
         for (IObserverFunction target : targets) {
            if(target instanceof IProgramMethod){
               IProgramMethod progMethod = (IProgramMethod) target;
               if(progMethod.getContainerType().getJavaType().equals(javaType)){
                  scl = KeYUtil.convertToSourceLocation(progMethod.getPositionInfo());
                  scl = KeYUtil.updateToMethodNameLocation(javaFile, scl);
               }
            }
            ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getContracts(type, target);
            for (Contract contract : contracts) {
               IFolder proofFolder = KeYResourcesUtil.getProofFolder(javaFile);
               IFile proofFile = KeYResourcesUtil.getProofFile(contract.getName(), proofFolder.getFullPath());
               IFile metaFile = KeYResourcesUtil.getProofMetaFile(proofFile);
               IMarker proofMarker = markerManager.getProofMarker(javaFile, scl, proofFile);
               List<IMarker> recursionMarker = markerManager.getRecursionMarker(javaFile, scl, proofFile);
               ProofElement pe = new ProofElement(javaFile, scl, environment, proofFolder, proofFile, metaFile, proofMarker, recursionMarker, contract);
               proofElements.add(pe);
            }
         }
      }
      for(ProofElement pe : proofElements){
         if(pe.getProofFile() != null && pe.getProofFile().exists()){
            try{
               ProofMetaFileReader pmfr = new ProofMetaFileReader(pe.getMetaFile());
               pe.setProofClosed(pmfr.getProofClosed());
               pe.setMarkerMsg(pmfr.getMarkerMessage());
               pe.setUsedContracts(KeYResourcesUtil.getProofElementsByProofFiles(pmfr.getUsedContracts(), proofElements));
            }
            catch (ProofMetaFileException e) {
               LogUtil.getLogger().logError(e);
            }
         }
      }
      return proofElements;
   }
   
   
   /**
    * Checks for every {@link ProofElement} if it is outdated.
    * @return a {@link List<ProofElement>} that contains the updated {@link ProofElements}.
    */
   private void setProofElementsOutdated() {
      List<ProofElement> proofsToCheck = getProofsToCheck();
      for(ProofElement pe : proofElements){
         if(buildType == KeYProjectBuildJob.CLEAN_BUILD 
               || (buildType == KeYProjectBuildJob.AUTO_BUILD && !KeYProjectProperties.isEnableBuildRequiredProofsOnly(project))){
            markerManager.setOutdated(pe);
         }
         else if(buildType == KeYProjectBuildJob.STARTUP_BUILD){
            buildOutdatedAndMissingProof(pe);
         }
         else if(buildType == KeYProjectBuildJob.MANUAL_BUILD_ALL_PROOFS){
               if(outdatedCheckElements == null){
                  markerManager.setOutdated(pe);
               }
               else if(outdatedCheckElements != null && proofsToCheck != null && proofsToCheck.contains(pe)){
                  markerManager.setOutdated(pe);
               }
         }
         else if(buildType == KeYProjectBuildJob.MANUAL_BUILD_OUTDATED_PROOFS){
            if(outdatedCheckElements == null){
               buildOutdatedAndMissingProof(pe);
            }
            else if(outdatedCheckElements != null && proofsToCheck != null && proofsToCheck.contains(pe)){
               buildOutdatedAndMissingProof(pe);
            }
         }
         else if(buildType == KeYProjectBuildJob.AUTO_BUILD){
            if(pe.getOutdated() || !hasProofFile(pe) || !hasMetaFile(pe) || !hasMarker(pe)){
               markerManager.setOutdated(pe);
            }
            else if(hasMetaFile(pe)){
               try{
                  ProofMetaFileReader pmfr = new ProofMetaFileReader(pe.getMetaFile());
                  LinkedList<IType> javaTypes = collectAllJavaITypes();
                  if(MD5changed(pe.getProofFile(), pmfr) || typeOrSubTypeChanged(pe, pmfr, javaTypes) || superTypeChanged(pe, javaTypes)){
                     markerManager.setOutdated(pe);
                  }
               }
               catch (Exception e){
                  markerManager.setOutdated(pe);
                  LogUtil.getLogger().logError(e);
               }
            }
         }        
      }
   }
   
   
   /**
    * Sorts all {@link ProofElement}s in the following order: Selected method, active editor proofs, open editor proofs, affected/outdated proofs, other proofs.
    * @param editorSelection - the current workbench state of the editor windows.
    */
   private void sortProofElements(EditorSelection editorSelection) {
      if(editorSelection != null){
         List<ProofElement> sortedProofs = new LinkedList<ProofElement>();
         //Active selection
         List<ProofElement> activeMethodProofs = new LinkedList<ProofElement>();
         IMethod selectedMethod = editorSelection.getSelectedMethod();
         IFile activeFile = editorSelection.getActiveFile();
         if(selectedMethod != null && activeFile != null && activeFile.exists() && activeFile.equals(selectedMethod.getResource())){
            activeMethodProofs = KeYResourcesUtil.getProofElementsForMethod(proofElements, selectedMethod);
         }
         sortedProofs.addAll(activeMethodProofs);
         //Proofs of active file
         List<ProofElement> activeFileProofs = getProofsForFile(activeFile);
         for(ProofElement pe : activeFileProofs){
            if(!activeMethodProofs.contains(pe)){
               sortedProofs.add(pe);
            }
         }
         //Open file proofs
         List<IFile> openFiles = editorSelection.getOpenFiles();
         List<ProofElement> openFilesProofs = new LinkedList<ProofElement>();
         for(IFile openFile : openFiles){
            openFilesProofs.addAll(getProofsForFile(openFile));
         }
         sortedProofs.addAll(openFilesProofs);
         //Outdated proofs
         List<ProofElement> outdatedProofs = new LinkedList<ProofElement>();
         for(ProofElement pe : proofElements){
            if(pe.getBuild() && !activeFileProofs.contains(pe) && !openFilesProofs.contains(pe)){
               outdatedProofs.add(pe);
            }
         }
         sortedProofs.addAll(outdatedProofs);
         //Other proofs
         List<ProofElement> otherProofs = new LinkedList<ProofElement>();
         for(ProofElement pe : proofElements){
            if(!activeFileProofs.contains(pe) && !openFilesProofs.contains(pe) && !outdatedProofs.contains(pe)){
               otherProofs.add(pe);
            }
         }
         sortedProofs.addAll(otherProofs);
         if(proofElements.size() == sortedProofs.size()){
            proofElements = sortedProofs;  
         }
         else{
            System.out.println("Not all or more proofs then available are sorted!");
         }
      }    
   }
   
   
   /**
    * Collects all {@link ProofElement}s associated with the given {@link IFile}.
    * @param file - the {@link IFile} to use
    * @return a {@link List<ProofElement>} with all associated {@link ProofElement}s
    */
   public List<ProofElement> getProofsForFile(IFile file){         
      List<ProofElement> fileProofs = new LinkedList<ProofElement>();
      IJavaElement javaElement = JavaCore.create(file);
      if(file != null && javaElement != null){
         for(ProofElement pe : proofElements){
            if(pe != null && file.equals(pe.getJavaFile())){
               fileProofs.add(pe);
            }
         }
      }
      else if (file != null && 
               (KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(file.getFileExtension()) || 
                KeYResourcesUtil.META_FILE_EXTENSION.equals(file.getFileExtension()))) {
         for(ProofElement pe : proofElements){
            if(pe != null && file.equals(pe.getProofFile())){
               fileProofs.add(pe);
               break;
            }
            else if(pe != null && file.equals(pe.getMetaFile())){
               fileProofs.add(pe);
               break;
            }
         }
      }
      return fileProofs;
   }
   
   
   private void cleanMarker() {
      List<IMarker> peMarker = new LinkedList<IMarker>();
      for(ProofElement pe : proofElements){
         IMarker proofMarker = pe.getProofMarker();
         if(proofMarker != null && proofMarker.exists()){
            peMarker.add(proofMarker);
         }
         List<IMarker> recursionMarker = pe.getRecursionMarker();
         for(IMarker marker : recursionMarker){
            if(marker != null && marker.exists()){
               peMarker.add(marker);
            }
         }
      }
      LinkedList<IMarker> allMarker = markerManager.getAllKeYMarker(project, IResource.DEPTH_INFINITE);
      for(IMarker marker : allMarker){
         if(!peMarker.contains(marker)){
            try{
               marker.delete();
            }
            catch (CoreException e){
               LogUtil.getLogger().logError(e);
            }
         }
      }
   }
   
   
   /**
    * Cleans every {@link IFolder} in the given {@link IFolder} by removing all files which are not 
    * listed in the given {@link LinkedList}. Empty {@link IFolder} will be deleted too.
    * @param proofFiles - the {@link LinkedList} to use
    * @param folder - the {@link IFolder} to start at
    * @throws CoreException
    */
   private void cleanProofFolder(LinkedList<IFile> proofFiles, IFolder folder) {
      if(folder.exists()){
         try{
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
         catch (CoreException e){
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   
   /**
    * Initializes the {@link Thread}s and creates the {@link ProofRunnable}s. While 
    * the {@link Thread}s are alive completed {@link Proof}s are saved periodically. 
    * @param proofElements
    * @param changedJavaFiles
    * @param monitor
    * @throws Exception 
    */
   private void initThreads(IProgressMonitor monitor) {
      proofQueue = Collections.synchronizedList(KeYResourcesUtil.cloneList(proofElements));

      int numOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      int numOfProofs = getNumOfProofsToDo();
      if(numOfProofs < numOfThreads){
         numOfThreads = numOfProofs;
      }
      Thread[] threads = null;
      if (KeYProjectProperties.isEnableMultiThreading(project) && numOfThreads >= 2) {
         threads = new Thread[numOfThreads];
         for (int i = 0; i < numOfThreads; i++) {

            ProofRunnable run = new ProofRunnable(project, proofElements, proofQueue, cloneEnvironment(), monitor);
            Thread thread = new Thread(run);
            threads[i] = thread;
         }
         for(Thread thread : threads){
            thread.start();
         }
      }
      else{
         ProofRunnable run = new ProofRunnable(project, proofElements,proofQueue, environment, monitor);
         Thread thread = new Thread(run);
         threads = new Thread[1];
         threads[0] = thread;
         thread.start();
      }
      
      while(threadsAlive(threads)){
         ObjectUtil.sleep(100); // TODO: Is it guaranteed that this terminates. May check for monitor.isCanceled()?
      }
   }
   
   
   private int getNumOfProofsToDo(){
      int num = 0;
      for(ProofElement pe : proofElements){
         if(pe.getBuild()){
            num++;
         }
      }
      return num;
   }
   
   
   
   /**
    * Returns if the given {@link Thread}s are alive.
    * @param threads - the {@link Thread}s to check
    * @return true if at least one {@link Thread} is alive. false otherwise
    */
   private boolean threadsAlive(Thread[] threads){
      for(Thread thread : threads){
         if (thread.isAlive()){
            return true;
         }
      }
      return false;
   }
   
   
   /**
    * Clones the global {@link KeYEnvironment}.
    * @return the cloned {@link KeYEnvironment}
    */
   private KeYEnvironment<CustomUserInterface> cloneEnvironment() {
      InitConfig sourceInitConfig = environment.getInitConfig();
      // Create new profile which has separate OneStepSimplifier instance
      JavaProfile profile = new JavaProfile();
      // Create new InitConfig and initialize it with value from initial one.
      InitConfig initConfig = new InitConfig(environment.getServices().copy(profile, false));
      initConfig.setActivatedChoices(sourceInitConfig.getActivatedChoices());
      ProofSettings clonedSettings = sourceInitConfig.getSettings() != null ? new ProofSettings(sourceInitConfig.getSettings()) : null;
      initConfig.setSettings(clonedSettings);
      initConfig.setTaclet2Builder(sourceInitConfig.getTaclet2Builder());
      initConfig.setTaclets(sourceInitConfig.getTaclets());
      // Create new ProofEnvironment and initialize it with values from initial one.
      initConfig.getServices().setJavaModel(sourceInitConfig.getServices().getJavaModel());
      KeYEnvironment<CustomUserInterface> keyEnv = new KeYEnvironment<CustomUserInterface>(new CustomUserInterface(false), initConfig);
      return keyEnv;
   }
   

   /**
    * Checks all given {@link ProofElement}s for cycling contract recursion
    * @param proofElements - the {@link ProofElement} to check
    * @throws CoreException
    */
   private void checkContractRecursion() throws CoreException {
      HashSet<List<ProofElement>> cycles = new HashSet<List<ProofElement>>();
      findCycles(cycles);
      removeAllRecursionMarker();
      for(List<ProofElement> cycle : cycles){
         markerManager.setRecursionMarker(cycle);
      }
      restoreOldMarkerForRemovedCycles();
   }
   
   
   /**
    * Collects all proof- and meta{@link IFile}s from the given {@link LinkedList} of {@link ProofElement}s.
    * @param proofElements - the {@link ProofElement}s to use
    * @return a {@link LinkedList} with all proof- and meta{@link IFile}s
    */
   private LinkedList<IFile> getAllFiles(){
      LinkedList<IFile> proofFiles = new LinkedList<IFile>();
      for(ProofElement pe : proofElements){
         proofFiles.add(pe.getProofFile());
         proofFiles.add(pe.getMetaFile());
      }
      return proofFiles;
   }
   
   
   private void buildOutdatedAndMissingProof(ProofElement pe){
      if(!hasProofFile(pe) || !hasMetaFile(pe) || !hasMarker(pe) || pe.getOutdated()){
         markerManager.setOutdated(pe);
      }
   }
   
   
   private List<ProofElement> getProofsToCheck(){
      if(outdatedCheckElements == null || !(buildType == KeYProjectBuildJob.MANUAL_BUILD_ALL_PROOFS || buildType == KeYProjectBuildJob.MANUAL_BUILD_OUTDATED_PROOFS)){
         return null;
      }
      else{
         List<ProofElement> proofsToCheck = new LinkedList<ProofElement>();
         for(Object obj : outdatedCheckElements){
            if(obj instanceof IFile){
               IFile file = (IFile) obj;
               for(ProofElement pe : proofElements){
                  if(pe != null){
                     if(file.equals(pe.getJavaFile()) || file.equals(pe.getProofFile())){
                        proofsToCheck.add(pe);
                     }
                  }
               }
            }
            else if(obj instanceof IMethod){
               IMethod method = (IMethod) obj;
               proofsToCheck.addAll(KeYResourcesUtil.getProofElementsForMethod(proofElements, method));
            }
         }
         return proofsToCheck;
      }
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
    * Collects all {@link IType}s of the given {@link IType}.
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
   private static boolean MD5changed(IFile proofFile, ProofMetaFileReader pmfr) throws IOException, CoreException{
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
      HashMap<String, List<String>> types = pmfr.getTypeElements();
      for(Map.Entry<String, List<String>> entry : types.entrySet()){
         String type = entry.getKey();
         List<String> subTypes = entry.getValue();
         if(typeChanged(type, javaTypes)){
            return true;
         }
         else if(subTypeChanged(pe, type, subTypes, javaTypes)){
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
   private boolean typeChanged(String type, List<IType> javaTypes) throws JavaModelException{
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
    * Checks if any subTypes of the given {@link ProofMetaFileTypeElement} were changed.
    * @param te - the {@link ProofMetaFileTypeElement} to use
    * @param javaTypes - all {@link IType}s of the project
    * @return true if any subTypes were changed. false otherwise
    * @throws JavaModelException
    */
   private boolean subTypeChanged(ProofElement pe, String type, List<String> subTypes, List<IType> javaTypes) throws JavaModelException{
      KeYJavaType kjt = getkeYJavaType(environment, type);
      ImmutableList<KeYJavaType> envSubKjts = environment.getJavaInfo().getAllSubtypes(kjt);      
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
      KeYJavaType envKjt = getkeYJavaType(environment, kjt.getFullName());
      if(envKjt != null){
         ImmutableList<KeYJavaType> envSuperKjts = environment.getJavaInfo().getAllSupertypes(envKjt);
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
   private IFile getJavaFileForType(String metaType, List<IType> typeList) throws JavaModelException{
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
   private KeYJavaType getkeYJavaType(KeYEnvironment<CustomUserInterface> env, String type){
      Set<KeYJavaType> envKjts = env.getServices().getJavaInfo().getAllKeYJavaTypes();
      for(KeYJavaType kjt : envKjts){
         if(type.equals(kjt.getFullName())){
            return kjt;
         }
      }
      return null;
   }

   
   private boolean hasProofFile(ProofElement pe){
      return (pe.getProofFile() != null && pe.getProofFile().exists());
   }
   
   
   private boolean hasMetaFile(ProofElement pe){
      return (pe.getMetaFile() != null && pe.getMetaFile().exists());
   }
   
   private boolean hasMarker(ProofElement pe){
      if(pe.getProofMarker() != null && pe.getProofMarker().exists()){
         return true;
      }
      else{
         if(pe.getRecursionMarker() != null && !pe.getRecursionMarker().isEmpty()){
            for(IMarker marker : pe.getRecursionMarker()){
               if(marker != null && marker.exists()){
                  return true;
               }
            }
         }
      }
      return false;
   }
   
   private void restoreOldMarkerForRemovedCycles() {
      for(ProofElement pe : proofElements){
         if(pe.getProofMarker() == null && (pe.getRecursionMarker() == null || pe.getRecursionMarker().isEmpty())){
            if(pe.getProofFile() != null && pe.getProofFile().exists()){
               markerManager.setMarker(pe);
            }
         }
      }
   }


   private void findCycles(HashSet<List<ProofElement>> cycles){
      for(ProofElement pe : proofElements){
         LinkedList<ProofElement> cycle = new LinkedList<ProofElement>();
         cycle.add(pe);
         searchCycle(cycle, cycles);
      }
   }
   
   private void searchCycle(List<ProofElement> cycle, HashSet<List<ProofElement>> cycles){
      List<ProofElement> succs = cycle.get(cycle.size()-1).getUsedContracts();
      for(ProofElement pe : succs){
         if(pe.equals(cycle.get(0))){
            //cycle found
            cycles.add(cycle);
         }
         else if(cycle.contains(pe)){
            return;
         }
         else{
            List<ProofElement> tmpCycle = KeYResourcesUtil.cloneList(cycle);
            tmpCycle.add(pe);
            searchCycle(tmpCycle, cycles); 
         }
      }
   }
   
   
   private void removeAllRecursionMarker() throws CoreException {
      for(ProofElement pe : proofElements){
         pe.setRecursionMarker(new LinkedList<IMarker>());
      }
      markerManager.deleteKeYMarkerByType(project, IResource.DEPTH_INFINITE, MarkerManager.RECURSIONMARKER_ID);
   }
}
