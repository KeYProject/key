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

import java.io.File;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javax.xml.transform.TransformerException;

import org.eclipse.core.resources.IContainer;
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
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
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
      if (environment != null) {
         environment.dispose();
      }
      for (Proof proof : proofs) {
         proof.dispose();
      }
   }
   
   

   /**
    * Runs all {@link Proof}s available in the {@link IProject} and saves them into the proof{@link IFolder}.
    * @param autoDeleteProofFiles - enables or deletes the automatically proof{@link IFile} deletion
    * @throws Exception
    */
   public void runAllProofs(boolean autoDeleteProofFiles, IProgressMonitor monitor) throws Exception{
      LinkedList<ProofElement> proofElements = getAllProofElements();
      LinkedList<IFile> javaFiles = getAllJavaFilesFromProofElements(proofElements);
      LinkedList<IFile> proofFiles = new LinkedList<IFile>();
      markerManager.deleteKeYMarker(javaFiles);
      markerManager.deleteKeYMarker(project);
      //set up monitor
      monitor.beginTask("Build all proofs", proofElements.size());
      for(ProofElement pe : proofElements){
         monitor.subTask("Build " + pe.getProofObl().name());
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
         monitor.worked(1);
      }
      if(autoDeleteProofFiles){
         cleanProofFolder(proofFiles, mainProofFolder);  
      }
      monitor.done();
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
         monitor.worked(1);
      }
      
      for(ProofElement pe : proofElements){
         checkContractRecursion(pe, proofElements);
      }
      
      if(autoDeleteProofFiles){
         cleanProofFolder(proofFiles, mainProofFolder);  
      }
      monitor.done();
   }
   
   
   private void checkContractRecursion(ProofElement pe, LinkedList<ProofElement> proofElements){
      LinkedList<Contract> proofRefContracts = getProofRefContracts(pe);
   }
   
   
   private LinkedList<Contract> getProofRefContracts(ProofElement pe){
      return null;
   }
   
   
   /**
    * Collects all {@link Proof}s available in the {@link IProject} and returns their
    * {@link ProofOblInput}s, java{@link IFiles}s and {@link SourceLocation}s as 
    * {@link ProofElement}s in a {@link LinkedList}.
    * @return - the {@link LinkedList} with all {@link ProofElement}s
    */
   private LinkedList<ProofElement> getAllProofElements() {
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
               proofElements.add(new ProofElement(obl, javaFile, scl, type, environment, contract));
            }
         }
      }
      return proofElements;
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
   private void cleanProofFolder(LinkedList<IFile> proofFiles, IFolder folder) throws CoreException{
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
         pe.getKeYEnvironment().getUi().startAndWaitForAutoMode(proof);
         pe.setProof(proof);
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
         if (proof != null) {
            proofs.add(proof);
            if (!proof.closed()){
               environment.getUi().startAndWaitForAutoMode(proof);
            }
         }
         return pe;
      }catch(Exception e){
         LogUtil.getLogger().createErrorStatus(e);
         e.printStackTrace();
         return null;
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
}
