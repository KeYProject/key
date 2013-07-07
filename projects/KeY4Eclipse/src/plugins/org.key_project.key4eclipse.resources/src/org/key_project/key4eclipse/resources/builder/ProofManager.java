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
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

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
import org.key_project.key4eclipse.resources.io.ProofMetaFileContentException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileTypeElement;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeY4EclipseResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProofStarter;

public class ProofManager {

   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private MarkerManager markerManager;
   private IFolder mainProofFolder;
   private IProject project;
   private List<IFile> changedJavaFiles = Collections.synchronizedList(new LinkedList<IFile>());
   private List<ProofElement> proofsToDo = Collections.synchronizedList(new LinkedList<ProofElement>());
   private List<Pair<ByteArrayOutputStream, ProofElement>> proofsToSave = Collections.synchronizedList(new LinkedList<Pair<ByteArrayOutputStream, ProofElement>>());

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
   
   
   public void runProofs(IProgressMonitor monitor) throws Exception{
      runProofs(new LinkedList<IFile>(), monitor);
   }

   /**
    * Runs all {@link Proof}s available in the {@link IProject} and saves them into the proof{@link IFolder}.
    * @param autoDeleteProofFiles - enables or deletes the automatically proof{@link IFile} deletion
    * @throws Exception
    */
   public void runProofs(LinkedList<IFile> changedJavaFiles, IProgressMonitor monitor) throws Exception{
      LinkedList<ProofElement> proofElements = getAllProofElements();
      this.changedJavaFiles.addAll(changedJavaFiles);
      markerManager.deleteKeYMarker(project, IResource.DEPTH_ZERO);
      //set up monitor
      monitor.beginTask("Build all proofs", proofElements.size());
      init(proofElements, changedJavaFiles, monitor);
      
      checkContractRecursion(proofElements);
      cleanMarker(proofElements);
      if(KeYProjectProperties.isAutoDeleteProofFiles(project)){
         cleanProofFolder(getAllFiles(proofElements), mainProofFolder);
      }
      monitor.done();
   }
   
   
   private void cleanMarker(LinkedList<ProofElement> proofElements) throws CoreException{
      LinkedList<IMarker> allMarker = markerManager.getAllKeYMarker(project);
      for(IMarker marker : allMarker){
         boolean delete = true;
         for(ProofElement pe : proofElements){
            SourceLocation scl = pe.getSourceLocation();
            int charStart = (Integer)marker.getAttribute(IMarker.CHAR_START);
            int charEnd = (Integer)marker.getAttribute(IMarker.CHAR_END);
            if(charStart == scl.getCharStart() && charEnd == scl.getCharEnd()){
               delete = false;
            }
         }
         if(delete){
            marker.delete();
         }
      }
   }
   
   private LinkedList<IFile> getAllFiles(LinkedList<ProofElement> proofElements){
      LinkedList<IFile> proofFiles = new LinkedList<IFile>();
      for(ProofElement pe : proofElements){
         proofFiles.add(pe.getProofFile());
         proofFiles.add(pe.getMetaFile());
      }
      return proofFiles;
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
   
   
   private boolean typeChanged(ProofMetaFileReader pmfr) throws Exception{
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
               IFolder proofFolder = getProofFolder(javaFile);
               proofElements.add(new ProofElement(javaFile, scl, environment, proofFolder, type, contract));
            }
         }
      }
      return proofElements;
   }
   
   
   private KeYEnvironment<CustomConsoleUserInterface> cloneEnvironment(){
      System.out.println("Cloning");

            InitConfig sourceInitConfig = environment.getInitConfig();
            //TODO was not used. check if thats ok
            //RuleJustificationInfo sourceJustiInfo = environment.getInitConfig().getProofEnv().getJustifInfo();
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
            InitConfig initConfig = new InitConfig(environment.getServices().copy(), profile);
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
            return keyEnv;
         }
   
   
   /**
    * Deletes the main Proof{@link IFolder} and runs all {@link Proof}s for the {@link IProject}.
    * @throws Exception
    */
   public void clean(boolean autoDeleteProofFiles, IProgressMonitor monitor) throws Exception{
      deleteResource(mainProofFolder);
      runProofs(monitor);
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
   private void deleteResource(IResource res) throws CoreException{
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
   
   
   private IFolder getProofFolder(IResource res){
      IPath proofFolderPath = mainProofFolder.getFullPath();
      IPath javaToProofPath = javaToProofPath(res.getFullPath());
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder proofFolder = root.getFolder(proofFolderPath.append(javaToProofPath));
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
   private void processProof(ProofElement pe) throws Exception{
      markerManager.deleteMarkerForSourceLocation(pe.getJavaFile(), pe.getSourceLocation());
      System.out.println(pe.getProofFile().getFullPath());
      
      IFile file = pe.getProofFile();
      if(!file.exists()){
         createProof(pe);
      }
      else{
         //TODO: extract mediator too
//         loadProof(pe);
         if(pe.getProof() == null){
            createProof(pe);
         }
      }
      markerManager.setMarker(pe.getProof(), pe.getSourceLocation(), pe.getJavaFile(), pe.getProofFile()); 
   }
   
   private OneStepSimplifier findOSS(Proof proof) {
      for (BuiltInRule bir : proof.env().getInitConfig().getProfile().getStandardRules().getStandardBuiltInRules()) {
         if (bir instanceof OneStepSimplifier) {
            return (OneStepSimplifier)bir;
         }
      }      
      return null;
   }
   
   
   /**
    * Creates a {@link Proof} for the given {@link ProofOblInput} and runs the AutoMode.
    * @param obl - the given {@link ProofOblInput}
    * @return the created {@link Proof}
    * @throws ProofInputException 
    */
   private void createProof(ProofElement pe) throws ProofInputException{
         Proof proof = pe.getKeYEnvironment().createProof(pe.getProofObl());
         
         ProofStarter ps = new ProofStarter();
         ps.init(new SingleProof(proof, pe.getProofObl().name()));
         
         OneStepSimplifier oss = findOSS(proof);
         if (oss != null) {
            oss.refresh(proof);
         }
         
         ps.start();
         pe.setProof(proof);
         pe.setProofReferences(ProofReferenceUtil.computeProofReferences(proof));
   }
   
   
   /**
    * Loads the {@link Proof} of the given {@link IFile} and runs the AutoMode.
    * @param file - the given {@link IFile}
    * @return the loaded {@link Proof}
    */
   private void loadProof(ProofElement pe){
      try{
         File file = pe.getProofFile().getLocation().toFile();
         KeYEnvironment<CustomConsoleUserInterface> loadEnv = KeYEnvironment.load(file, null, null);
         Proof proof = loadEnv.getLoadedProof();
         if (proof != null) {
            if (!proof.closed()){
               ProofStarter ps = new ProofStarter();
               ps.init(new SingleProof(proof, pe.getProofObl().name()));
               
               OneStepSimplifier oss = findOSS(proof);
               if (oss != null) {
                  oss.refresh(proof);
               }
               ps.start();
            }
            pe.setProof(proof);
            pe.setProofReferences(ProofReferenceUtil.computeProofReferences(proof));
         }
      }catch(Exception e){
         LogUtil.getLogger().createErrorStatus(e);
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
      markerManager.deleteKeYMarker(project, IResource.DEPTH_ZERO);
      LinkedList<IFile> allFiles = collectAllJavaFilesForProject();
      for(IFile file : allFiles){
         markerManager.deleteKeYMarker(file, IResource.DEPTH_ZERO);
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
   
   


   
   private ProofElement getProofToDo() {
      ProofElement pe = null;
      synchronized (proofsToDo) {
         if (!proofsToDo.isEmpty()) {
            pe = proofsToDo.remove(0);
         }
      }
      return pe;
   }
   
   
   
   public void init(LinkedList<ProofElement> proofElements, LinkedList<IFile> changedJavaFiles, IProgressMonitor monitor) throws InterruptedException, CoreException {
      
      proofsToDo = Collections.synchronizedList((LinkedList<ProofElement>)proofElements.clone());

      // Fill proofsToDO;
      int numOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      if (KeYProjectProperties.isEnableMultiThreading(project) && numOfThreads >= 2) {
         Thread[] threads = new Thread[numOfThreads];
         for (int i = 0; i < numOfThreads; i++) {

            ProofRunnable run = new ProofRunnable(cloneEnvironment(), monitor);
            Thread thread = new Thread(run);
            threads[i] = thread;
         }
         for(Thread thread : threads){
            thread.start();
         }
         while(threadsAlive(threads)){
            ObjectUtil.sleep(1000);
            saveProofsFormList();
         }
         saveProofsFormList();
         
      }
      else {
         ProofRunnable run = new ProofRunnable(cloneEnvironment(), monitor);
         run.run();
         saveProofsFormList();
      }
      // Set marker
      System.out.println("Done");
   }
   
   
   private boolean threadsAlive(Thread[] threads){
      for(Thread thread : threads){
         if (thread.isAlive()){
            return true;
         }
      }
      return false;
   }
   
   
   private ByteArrayOutputStream generateSaveProof(Proof proof, IFile file) throws CoreException {
      Assert.isNotNull(proof);
      Assert.isNotNull(file);
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
   
   private void saveProof(ByteArrayOutputStream out, ProofElement pe) throws CoreException{
      // Save proof file content
      IFile file = pe.getProofFile();
      createProofFolder(file);
      if (file.exists()) {
         file.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
      }
      else {
         file.create(new ByteArrayInputStream(out.toByteArray()), true, null);
      }
   }
   
   
   private void saveProofsFormList() throws CoreException{
      while(!proofsToSave.isEmpty()){
         Pair<ByteArrayOutputStream, ProofElement> pairToSave = proofsToSave.remove(0);
         ByteArrayOutputStream out = pairToSave.first;
         ProofElement pe = pairToSave.second;
         saveProof(out, pe);
         ProofMetaFileWriter pmfw = new ProofMetaFileWriter();
         IFile metaFile = pmfw.writeMetaFile(pe);
         pe.setMetaFile(metaFile);
      }
   }


   

   private class ProofRunnable implements Runnable {
      
      private KeYEnvironment<CustomConsoleUserInterface> environment;
      private IProgressMonitor monitor;
      
      public ProofRunnable(KeYEnvironment<CustomConsoleUserInterface> environment, IProgressMonitor monitor){
         this.environment = environment;
         this.monitor = monitor;
      }
      
      @Override
      public void run() {
         try{
            ProofElement pe;
            while ((pe = getProofToDo()) != null) {

               pe.setKeYEnvironment(environment);
               pe.setProofObl(pe.getContract().createProofObl(environment.getInitConfig(), pe.getContract()));
               pe.setProofFile(getProofFile(pe.getProofObl().name(), pe.getProofFolder().getFullPath()));

               monitor.subTask("Building " + pe.getProofObl().name());
               
               if(!KeYProjectProperties.isEnableEfficientProofManagement(project)){
                  processProof(pe);                
                  
               }
               else{
                  IFile metaFile = getProofMetaFile(pe.getProofFile());
                  if(metaFile.exists()){
                     ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
                     if(sameHashCode(pe.getProofFile(), pmfr)){
                        if(typeChanged(pmfr)){
                           processProof(pe);
                        }
                        else{
                           if(subTypesChanged(pmfr)){
                              processProof(pe);
                           }
                        }
                     }
                     else{
                        processProof(pe);
                     }
                  }
                  else{
                     processProof(pe);
                  }
               }
               
               if(pe.getProof() != null){
                  ByteArrayOutputStream out = generateSaveProof(pe.getProof(), pe.getProofFile());
                  proofsToSave.add(new Pair<ByteArrayOutputStream, ProofElement>(out, pe));
                  
                  OneStepSimplifier oss = findOSS(pe.getProof());
                  if (oss != null) {
                     oss.refresh(null);
                  }
                  pe.getProof().dispose();
               }
               monitor.worked(1);
            }
            environment.dispose();
      
         } catch(Exception e){
         e.printStackTrace();
         }
      }
   }
   
   

}
