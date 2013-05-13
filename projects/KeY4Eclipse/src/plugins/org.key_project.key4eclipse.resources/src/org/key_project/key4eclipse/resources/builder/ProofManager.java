package org.key_project.key4eclipse.resources.builder;

import java.io.File;
import java.lang.reflect.Method;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

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
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.util.KeY4EclipseResourcesUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class ProofManager {

   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private MarkerManager markerManager;
   private IFolder mainProofFolder;
   
   public ProofManager(IProject project) throws CoreException, ProblemLoaderException{
      markerManager = new MarkerManager();
      createMainProofFolder(project);
      final File location = ResourceUtil.getLocation(project);
      final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
      final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
      environment = KeYEnvironment.load(location, classPaths, bootClassPath);
   }
   
   
   /**
    * Runs all {@link Proof}s of the given {@link IResource}, sets {@link IMarker} and saves the {@link Proof}s.
    * @param res - the given {@link IResource}
    * @throws Exception
    */
   public void runProofsForResource(IResource res) throws Exception{
      //get all methods from the given resource.
      LinkedList<IFile> proofFiles = new LinkedList<IFile>();
      LinkedList<IMethod> methods = getResourceMethods(res);
      if(methods != null){
         //creates the folder structure for the given resource
         IFolder proofFolder = createProofFolder(res);
         //run proofs for each method
         for(IMethod method : methods){
            LinkedList<ProofOblInput> proofObls = createProofOblsForMethod(method);
            for(ProofOblInput obl : proofObls){
               IFile proofFile = getProofFile(obl.name(), proofFolder.getFullPath());
               proofFiles.add(proofFile);
               Proof proof = processProof(obl, proofFile);
               markerManager.setMarker(proof, method, proofFile);
               KeY4EclipseResourcesUtil.saveProof(proof, proofFile);
            }
         }
         //delete proof files which don't belong to any method
         deleteUnnecessaryProofFiles(proofFolder, proofFiles);
      }
   }
   
   
   /**
    * Reruns the deleted proof that was stored in the given {@link IResource} and saves it again.
    * @param res - a deleted {@link IResource} proof file
    * @throws Exception
    */
   public void rerunProofsForDeletedProofFiles(IResource res) throws Exception{
      IResource javaFile = getJavaFileForProofFile(res);
      if(javaFile != null){
         LinkedList<IMethod> methods = getResourceMethods(javaFile);
         IFolder proofFolder = createProofFolder(javaFile);
         for(IMethod method : methods){
            LinkedList<ProofOblInput> proofObls = createProofOblsForMethod(method);
            
            for(ProofOblInput obl : proofObls){
               IFile proofFile = getProofFile(obl.name(), proofFolder.getFullPath());
               if(!proofFile.exists()){
                  Proof proof = processProof(obl, proofFile);
                  KeY4EclipseResourcesUtil.saveProof(proof, proofFile);
               }
            }
         }
      }
   }
   
   
   /**
    * Deletes all KeY-{@link IMarker} from the given {@link IResource}.
    * @param res - the given {@link IResource}
    * @throws CoreException
    */
   public void deleteMarker(IResource res) throws CoreException{
      markerManager.deleteMarker(res);
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
    * Deletes the Proof-{@link IFolder} for the given Java-{@link IResource}.
    * @param res - the Java-{@link IResource}
    * @throws CoreException
    */
   public void deleteProofFolderForJavaFile(IResource res) throws CoreException{
      IFolder folder = getProofFolderForJavaFile(res);
      deleteResource(folder);
   }

   
   /**
    * Deletes all not longer required Proof-{@link IFile}s from the given {@link IFolder}. After that all empty {@link IFolder}s above will be deleted.
    * @param folder - the Proof-{@link IFolder}
    * @param files - the {@link IFile}s to keep
    * @throws CoreException
    */
   private void deleteUnnecessaryProofFiles(IFolder folder, LinkedList<IFile> files) throws CoreException{
      IResource[] members = folder.members();
      for(IResource member : members){
         if(member.getType() == IResource.FILE){
            if(!files.contains(member)){
               member.delete(true, null);
            }
         }
      }
      members = folder.members();
      if(members.length == 0){
         deleteUnnecessaryFolders(folder);
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
    * Creates the main proofFolder for the given {@link IProject}. For example: /Project/Proofs/
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   private void createMainProofFolder(IProject project) throws CoreException{
      IPath projectPath = project.getFullPath();
      IPath proofFolderPath = projectPath.append("Proofs");
      IFolder proofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofFolderPath);
      if(!proofFolder.exists()){
         proofFolder.create(true, true, null);       
      }
      mainProofFolder = proofFolder;
   }
   
   
   /**
    * Creates the proofFolderStructure for the given {@link IResource}.
    * @param res - the given {@link IResource}
    * @return the created {@link IFolder}
    * @throws CoreException
    */
   private IFolder createProofFolder(IResource res) throws CoreException{
      IFolder proofFolder = mainProofFolder;
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
   private Proof processProof(ProofOblInput obl, IFile file) throws Exception{      
      Proof proof;
      if(!file.exists()){
         proof = environment.createProof(obl);
         environment.getUi().startAndWaitForAutoMode(proof);   
      }
      else{
         File proofFile = file.getLocation().toFile();
         environment = KeYEnvironment.load(proofFile, null, null);
         proof = environment.getLoadedProof();
         if(!proof.closed()){
            environment.getUi().startAndWaitForAutoMode(proof);
         }
      }
      return proof;  
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
   
   
   /**
    * Collects all {@link IMethod}s in the given {@link IResource}.
    * @param res - the given {@link IResource}
    * @return - the {@link LinkedList<IMethod>} with all {@link IMethod}s
    * @throws JavaModelException
    */
   private LinkedList<IMethod> getResourceMethods(IResource res) throws JavaModelException{
      ICompilationUnit unit = (ICompilationUnit) JavaCore.create(res);
      LinkedList<IMethod> methods = new LinkedList<IMethod>();
      IType[] types = unit.getAllTypes();
      for(IType type : types){
         IMethod[] tmp = type.getMethods();
         for(IMethod method : tmp){
            methods.add(method);
         }
      }
      return methods;
   }

   
   /**
    * Creates all {@link ProofOblInput}s for the given {@link IMethod}.
    * @param method - the {@link IMethod to use
    * @return - the {@link LinkedList<IMethod>} with all {@link ProofOblInput}s
    * @throws ProofInputException
    */
   private LinkedList<ProofOblInput> createProofOblsForMethod(IMethod method) throws ProofInputException{
      LinkedList<ProofOblInput> proofObls = new LinkedList<ProofOblInput>();
      ImmutableSet<FunctionalOperationContract>  contracts = createContractsForMethod(method);
      Iterator<FunctionalOperationContract> it = contracts.iterator();
      while (it.hasNext()) {
         FunctionalOperationContract contract = it.next();
         ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
         proofObls.add(input);
      }
      return proofObls;
   }
   
   
   /**
    * Collects all {@link FunctionalOperationContract}s of the given {@link IMethod}.
    * @param method - the given {@link Method}.
    * @param environment - the {@link KeYEnvironment} for this {@link IMethod}.
    * @return - An {@link ImmutableSet<FunctionOperationContract>} that holds all {@link FunctionalOperationContract}s found for the given {@link IMethod}.
    * @throws ProofInputException
    */
   private ImmutableSet<FunctionalOperationContract> createContractsForMethod(IMethod method) throws ProofInputException {
      if (method != null && method.exists()) {
            if(environment.getInitConfig() != null){
               IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getJavaInfo());
               if(pm != null){
                  KeYJavaType type = pm.getContainerType();
                  ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(type, pm);
                  return operationContracts;
               }
            }
      }
      return null;
   }
   
   
   /**
    * Replaces invalid characters in the given {@link String} with '_' and returns a valid {@link String}.
    * @param str - the {@link String} to be made valid.
    * @return the valid {@link String}
    */
   //TODO: In Util stecken?
   private String makePathValid(String str){
      String tmp;
      for(int i = 1; i<=str.length();i++){
         tmp = str.substring(0, i);
         Path path = new Path(tmp);
         if(!path.isValidSegment(tmp)){
            StringBuilder strbuilder = new StringBuilder(str);
            strbuilder.setCharAt(i-1, '_');
            str = strbuilder.toString();
         }
      }
      return str;
   }
   
   
   /**
    * Returns the Proof-{@link IFolder} for a given Java-{@link IResource}
    * @param res - the given Java-{@link IResource}
    * @return - the Proof-{@link IFolder}
    */
   private IFolder getProofFolderForJavaFile(IResource res){
      IPath proofFolderPath = mainProofFolder.getFullPath();
      IPath innerProofFolderPath = javaToProofPath(res.getFullPath());
      proofFolderPath = proofFolderPath.append(innerProofFolderPath);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFolder folder = root.getFolder(proofFolderPath);
      if(folder.exists()){
         return folder;
      }
      else{
         return null;
      }
   }
   
   
   /**
    * Returns the Java-{@link IResource} for the given Proof-{@link IResource}
    * @param res - the given Proof-{@link IResource}
    * @return the Java-{@link IFile}
    */
   private IResource getJavaFileForProofFile(IResource res){
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
   
   
}
