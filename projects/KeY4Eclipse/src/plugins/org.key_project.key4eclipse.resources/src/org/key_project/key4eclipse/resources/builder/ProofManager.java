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
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.EditorSelection;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.util.eclipse.ResourceUtil;

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

   private KeYEnvironment<CustomUserInterface> environment;
   private MarkerManager markerManager;
   private IFolder mainProofFolder;
   private IProject project;
   private List<ProofElement> proofElements;
   private List<IFile> changedJavaFiles;
   private List<ProofElement> proofsToDo = Collections.synchronizedList(new LinkedList<ProofElement>());

   
   /**
    * The Constructor that loads the {@link KeYEnvironment}. If that fails the problemLoaderException will be set.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    * @throws ProblemLoaderException 
    */
   public ProofManager(IProject project) throws CoreException, ProblemLoaderException{
      this.project = project;
      markerManager = new MarkerManager();
      mainProofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME));
      changedJavaFiles = new LinkedList<IFile>();     
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
    * Runs the {@link Proof}s available in the {@link IProject} dependent on the ProofManageMentProperties.
    * @param changedJavaFiles - {@link LinkedList} with all changed java{@link IFile}s
    * @param monitor - the {@link IProgressMonitor}
    * @throws Exception
    */
   public void runProofs(IProgressMonitor monitor, EditorSelection editorSelection) throws Exception{
      KeYProjectDelta keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
      changedJavaFiles = keyDelta.getChangedJavaFiles();
      keyDelta.reset();
      markerManager.deleteKeYMarkerByType(project, IResource.DEPTH_ZERO, MarkerManager.PROBLEMLOADEREXCEPTIONMARKER_ID);
      proofElements = getAllProofElements();
//      sortProofElements(editorSelection);
      setOutdated();
      //set up monitor
      monitor.beginTask("Build all proofs", proofElements.size());
      initThreads(monitor);
      checkContractRecursion();
      cleanMarker();
      if(KeYProjectProperties.isAutoDeleteProofFiles(project)){
         cleanProofFolder(getAllFiles(), mainProofFolder);
      }
      monitor.done();
   }
   
   
//   private void sortProofElements(EditorSelection editorSelection) {
//      List<ProofElement> sortedProofs = new LinkedList<ProofElement>();
//      
//      List<ProofElement> activeEditorProofs = new LinkedList<ProofElement>();
//      if(editorSelection.getActiveEditor() != null){
//         ITextEditor activeEditor = editorSelection.getActiveEditor();
//         IFile file = ((IFileEditorInput) activeEditor.getEditorInput()).getFile();
//         for(ProofElement pe : proofElements){
//            if(pe.getJavaFile() != null && pe.getJavaFile().equals(file)){
//               activeEditorProofs.add(pe);
//            }
//         }
//         sortedProofs.addAll(activeEditorProofs);
//      }
      
//      file = ((IFileEditorInput) activeEditor.getEditorInput()).getFile();
//      IJavaElement javaElement = JavaCore.create(file);
//      ITextSelection selection = (ITextSelection) editorSelection.getActiveSelection();
//      if(javaElement instanceof ICompilationUnit){
//         try{
//            ICompilationUnit compUnit = (ICompilationUnit) javaElement;
//            IJavaElement selected = compUnit.getElementAt(selection.getOffset());
//            if(selected != null && selected.getElementType() == IJavaElement.METHOD){
//               IMethod method = (IMethod) selected;
//               ISourceRange range = method.getSourceRange();
//               int offset = range.getOffset();
//               int length = range.getLength();
//               int end = offset+length;
//
//               for(ProofElement pe : activeEditorProofs){
//                  SourceLocation scl = pe.getSourceLocation();
//                  int startScl = scl.getCharStart();
//                  int endScl = scl.getCharEnd();
//               }
//            }
//         }
//         catch(JavaModelException e){
//            LogUtil.getLogger().logError(e);
//         }
//      }

//      List<ProofElement> openEditorProofs = new LinkedList<ProofElement>();
//      if(editorSelection.getOpenEditors() != null){
//         for(ITextEditor editor : editorSelection.getOpenEditors()){
//            IFile file = ((IFileEditorInput) editor.getEditorInput()).getFile();
//            for(ProofElement pe : proofElements){
//               if(pe.getJavaFile() != null && pe.getJavaFile().equals(file)){
//                  openEditorProofs.add(pe);
//               }
//            }
//         }
//         sortedProofs.addAll(openEditorProofs);
//      }
//
//      List<ProofElement> outdatedProofs = new LinkedList<ProofElement>();
//      
//      for(ProofElement pe : proofElements){
//         if(pe.getOutdated = true && !activeEditorProofs.contains(pe) && !openEditorProofs.contains(pe)){
//            outdatedProofs.add(pe);
//         }
//         sortedProofs.addAll(outdatedProofs);
//      }
//      
//      List<ProofElement> otherProofs = new LinkedList<ProofElement>();
//      
//      for(ProofElement pe : proofElements){
//         if(!activeEditorProofs.contains(pe) && !openEditorProofs.contains(pe) && !outdatedProofs.contains(pe)){
//            otherProofs.add(pe);
//         }
//         sortedProofs.addAll(otherProofs);
//      }
//      proofElements = sortedProofs;
//   }
   
   
   private void setOutdated(){
      OutdatedChecker poc = new OutdatedChecker(project, proofElements, changedJavaFiles, environment);
      List<ProofElement> outdatedProofs = poc.getOutdatedProofs();
      
      for(ProofElement pe : outdatedProofs){
         markerManager.setOutdated(pe, true);
      }
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
               IFolder proofFolder = getProofFolder(javaFile);
               IFile proofFile = getProofFile(contract.getName(), proofFolder.getFullPath());
               IFile metaFile = getProofMetaFile(proofFile);
               IMarker proofMarker = markerManager.getProofMarker(javaFile, scl, proofFile);
               List<IMarker> recursionMarker = markerManager.getRecursionMarker(javaFile, scl, proofFile);
               proofElements.add(new ProofElement(javaFile, scl, environment, proofFolder, proofFile, metaFile, proofMarker, recursionMarker, contract));
            }
         }
      }
      return proofElements;
   }

   /**
    * Returns the proofFolder for the given java{@link IFile}.
    * @param javaFile - the java{@link IFile} to use
    * @return the proof{@link IFolder}
    */
   private IFolder getProofFolder(IFile javaFile){
      IPath proofFolderPath = mainProofFolder.getFullPath();
      IPath javaToProofPath = javaToProofPath(javaFile.getFullPath());
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = root.getFolder(proofFolderPath.append(javaToProofPath));
      return proofFolder;
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
    * Initializes the {@link Thread}s and creates the {@link ProofRunnable}s. While 
    * the {@link Thread}s are alive completed {@link Proof}s are saved periodically. 
    * @param proofElements
    * @param changedJavaFiles
    * @param monitor
    * @throws Exception 
    */
   private void initThreads(IProgressMonitor monitor) throws Exception {
      proofsToDo = Collections.synchronizedList(KeYResourcesUtil.cloneList(proofElements));

      int numOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      int numOfProofs = proofElements.size();
      if(numOfProofs < numOfThreads){
         numOfThreads = numOfProofs;
      }
      Thread[] threads = null;
      if (KeYProjectProperties.isEnableMultiThreading(project) && numOfThreads >= 2) {
         threads = new Thread[numOfThreads];
         for (int i = 0; i < numOfThreads; i++) {

            ProofRunnable run = new ProofRunnable(project, proofElements, proofsToDo, cloneEnvironment(), monitor);
            Thread thread = new Thread(run);
            threads[i] = thread;
         }
         for(Thread thread : threads){
            thread.start();
         }
      }
      else{
         ProofRunnable run = new ProofRunnable(project, proofElements,proofsToDo, environment, monitor);
         Thread thread = new Thread(run);
         threads = new Thread[1];
         threads[0] = thread;
         thread.start();
      }
      
      while(threadsAlive(threads)){
//         ObjectUtil.sleep(1000);
      }
   }
   
   
   /**
    * Returns if the given {@link Thread}s are alive.
    * @param threads - the {@link Thread}s th check
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
   

   /**
    * Checks all given {@link ProofElement}s for cycling contract recursion
    * @param proofElements - the {@link ProofElement} to check
    * @throws CoreException
    */
   private void checkContractRecursion() throws CoreException{
      findCycles();
      removeAllRecursionMarker();
      for(List<ProofElement> cycle : cycles){
         markerManager.setRecursionMarker(cycle);
      }
      restoreOldMarkerForRemovedCycles();
   }
   
   private void restoreOldMarkerForRemovedCycles() throws CoreException{
      for(ProofElement pe : proofElements){
         if(pe.getProofMarker() == null){
            markerManager.setMarker(pe);
         }
      }
   }
   
   private HashSet<List<ProofElement>> cycles;
   private void findCycles(){
      cycles = new HashSet<List<ProofElement>>();
      for(ProofElement pe : proofElements){
         LinkedList<ProofElement> cycle = new LinkedList<ProofElement>();
         cycle.add(pe);
         searchCycle(cycle);
      }
   }
   
   private void searchCycle(List<ProofElement> cycle){
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
            searchCycle(tmpCycle); 
         }
      }
   }
   
   
   private void removeAllRecursionMarker() throws CoreException{
      for(ProofElement pe : proofElements){
         pe.setRecursionMarker(new LinkedList<IMarker>());
      }
      markerManager.deleteKeYMarkerByType(project, IResource.DEPTH_INFINITE, MarkerManager.RECURSIONMARKER_ID);
   }
   
   
   private void cleanMarker() throws CoreException{
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
            marker.delete();
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
   private void cleanProofFolder(LinkedList<IFile> proofFiles, IFolder folder) throws CoreException{
      if(folder.exists()){
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
    * Returns the proof{@link IFile} for the given {@link String} and {@link IPath}.
    * @param name - the name for the {@link IFile}
    * @param path - the {@link IPath} for the {@link IFile} 
    * @return - the {@link IFile} for the Proof
    */
   private IFile getProofFile(String name, IPath path) {
      if (path != null && name != null) {
         name = ResourceUtil.validateWorkspaceFileName(name);
         name = name + "." + KeYUtil.PROOF_FILE_EXTENSION;
         path = path.append(name);
         IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
         return file;
      }
      else return null;
   }
   
   
   /**
    * Returns the metaFile of the given proof{@link IFile}
    * @param proofFile - the proof{@link IFile} to use
    * @return the meta{@link IFile}
    */
   private IFile getProofMetaFile(IFile proofFile){
      IPath proofFilePath = proofFile.getFullPath();
      IPath proofMetaFilePath = proofFilePath.removeFileExtension().addFileExtension(KeYResourcesUtil.META_FILE_EXTENSION);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile proofMetaFile = root.getFile(proofMetaFilePath);
      return proofMetaFile;
   }
}
