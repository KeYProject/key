package org.key_project.key4eclipse.resources.builder;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.jdt.internal.core.PackageFragment;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;



@SuppressWarnings("restriction")
public class KeYProjectBuilder extends IncrementalProjectBuilder {
   
   private BackgroundProofList proofList;
   

   public KeYProjectBuilder() {
   }

   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IResourceDelta delta = this.getDelta(getProject());
      if(delta != null){
         if(delta.getKind() == (IResourceDelta.CHANGED)){
            LinkedList<IMethod> methods = collectAllMethods(delta.getResource().getProject());
            if(!methods.isEmpty()){
               runProofs(methods, delta.getResource().getProject());
            }
         }
      }
      return null;
   }
   
   
   /**
    * Iterates over the given {@link LinkedList<IMethod>}. For each {@link IMethod} the {@link FunctionalOperationContract}s are collected. 
    * When a {@link Proof} for the current {@link FunctionalOperationContract} already exists it will be loaded and the AutoMode will be started.
    * If the {@link Proof} doesn't exists  it will be instantiated and then the AutoMode will be started. When the AutoMode is done, the {@link Proof} will be saved in a local directory.
    * @param methods - the {@link LinkedList<IMehod>} with the {@link IMetod}s for which the {@link Proof}s should run.
    * @throws CoreException 
    */
   private void runProofs(LinkedList<IMethod> methods, IProject project) throws CoreException{
      LinkedList<IFile> proofFileList = new LinkedList<IFile>();
      for(IMethod method : methods){
         try{
            //Initialize KeYEnvironment for this method
            final File location = ResourceUtil.getLocation(project);
            final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
            final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
            
            KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(location, classPaths, bootClassPath);
            
            ImmutableSet<FunctionalOperationContract> operationContracts = collectAllContractsForMethod(method, environment);
            
            
            //Create Folder for Proofs of this ;Method
            IPath folderPath = null;
            if(!operationContracts.isEmpty()){
               folderPath = createProofFolder(method);   
            }
            
            Iterator<FunctionalOperationContract> it = operationContracts.iterator();
            while(it.hasNext()){
               FunctionalOperationContract contract = it.next();
               ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
               //if proof does not exist, create it. else load it and run the automode.
               IFile file = createProofIFile(input.name(), folderPath);
               Proof finalProof = null;
               if(!file.exists()){
                  Proof proof = environment.createProof(input);
                  environment.getUi().startAndWaitForAutoMode(proof);
                  saveProof(proof, folderPath);
                  finalProof = proof;
                  
               }
               else{
                  File proofFile = file.getLocation().toFile();
                     environment = KeYEnvironment.load(proofFile, null, null);
                     Proof proof = environment.getLoadedProof();
                     if(!proof.closed()){
                        environment.getUi().startAndWaitForAutoMode(proof);
                        saveProof(proof, folderPath);
                     }
                     finalProof = proof;
                     
               }
               //add the proofFile to the proofFileList
               proofFileList.add(file);
               System.out.println("Add: " + file.getName());
               
               //set the marker for this proof
               setMarker(finalProof, method );               
            }
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
         }
         
      }  
      for(IFile file : proofFileList){
         System.out.println(file.getName());
      }
      cleanProofFolder(proofFileList, project);
   }
   
   
   
   private void cleanProofFolder(LinkedList<IFile> proofFileList, IProject project) throws CoreException {
      IPath proofPath = project.getFullPath();
      proofPath = proofPath.append("Proofs");
      System.out.println("proofPath:" + proofPath);
      IFolder proofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofPath);
      IResource[] members = proofFolder.members();
      for(IResource file : members){
         System.out.println(file.getName() + "       " + file.getClass());
         if(file instanceof File){
            if(!proofFileList.contains(file)){
               IContainer parent = file.getParent();
               file.delete(true, null);
               cleanParentFolders(parent);
            }
         }
      }
   }
   
   private void cleanParentFolders(IContainer parent) throws CoreException{
      
   if(parent instanceof IFolder){
      IFolder parentFolder = (IFolder)parent;
      if(parentFolder.members() == null || parentFolder.members().length == 0){
         IContainer pParent = parentFolder.getParent();
         parentFolder.delete(true, null);
         cleanParentFolders(pParent);
      } 
   }
   }   

   /**
    * Collects all {@link IMethod} of the given {@link IResourceDelta}s {@link IProject}.
    * @param delta - the {@link IResourceDelta} for which the {@link IMethod}s will be collected.
    * @return the {@link LinkedList<IMethod>} that contains the collected {@link IMethod}s.
    * @throws JavaModelException - possible Exception form the {@link JavaProject}s {@link PackageFragment}.
    */
   private LinkedList<IMethod> collectAllMethods(IProject project) throws JavaModelException{
      IJavaProject javaProject = JavaCore.create(project);
      IPackageFragment[] packages = javaProject.getPackageFragments();
      LinkedList<IMethod> methods = new LinkedList<IMethod>();
      for(IPackageFragment aPackage : packages){
         if (aPackage.getKind() == IPackageFragmentRoot.K_SOURCE) {
            
          //find Java Classes
            for (ICompilationUnit unit : aPackage.getCompilationUnits()) {
               IType[] allTypes = unit.getAllTypes();
               for (IType type : allTypes) {
                  IMethod[] classMethods = type.getMethods();
                  for(IMethod method : classMethods){
                     methods.add(method);
                  }
               }
            }         
         }
      }
      return methods;
   }
   
   
   /**
    * Collects all {@link FunctionalOperationContract}s of the given {@link IMethod}.
    * @param method - the given {@link Method}.
    * @param environment - the {@link KeYEnvironment} for this {@link IMethod}.
    * @return - An {@link ImmutableSet<FunctionOperationContract>} that holds all {@link FunctionalOperationContract}s found for the given {@link IMethod}.
    * @throws ProofInputException
    */
   private ImmutableSet<FunctionalOperationContract> collectAllContractsForMethod(IMethod method, KeYEnvironment<CustomConsoleUserInterface> environment) throws ProofInputException {
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
   
   
   private IPath splitPackageString(IPath path){
      IPath folderPath = path;
      while(!folderPath.segment(0).equals("src")){
         folderPath = folderPath.removeFirstSegments(1);
      }
      folderPath = folderPath.removeFirstSegments(1);
      
      return folderPath;
   }
   
   
   /**
    * Creates a {@link IFolder} for the {@link Proof}s of the given {@link IMethod}. The folder is named after the classname of the {@link IMethod}.
    * The classfolder will be a subfolder of the mainfolder "Proofs". This folder will be created if it doesn't exists.
    * @param method
    * @return
    * @throws CoreException
    */
   private IPath createProofFolder(IMethod method) throws CoreException{
      //create proofsProofFolder
      IPath javaProjectPath = method.getJavaProject().getPath();
      IPath proofProofFolderPath = javaProjectPath.append("Proofs");
      IFolder proofProofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofProofFolderPath);
      if(!proofProofFolder.exists()){
         proofProofFolder.create(true, true, null);
      }
      
      //create proofsPackageFolders
      IPath path = splitPackageString(method.getResource().getFullPath());
      IPath proofPackageFolderPath = proofProofFolderPath;
      for(String folder : path.segments()){
         proofPackageFolderPath = proofPackageFolderPath.append(folder);
         IFolder proofPackageFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofPackageFolderPath);
         if(!proofPackageFolder.exists()){
            proofPackageFolder.create(true, true, null);
         }
      }
      
      return proofPackageFolderPath;
      
   }
   
   
   /**
    * Creates the {@link IFile} for the {@link Proof} that will be stored.
    * @param name - the name for the {@link IFile}.
    * @param path - the path for the {@link IFile}.
    * @return - the {@link IFile}.
    */
   private IFile createProofIFile(String name, IPath path){
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
    * Replaces invalid characters in the given {@link String} with '_' and returns a vaild {@link String}.
    * @param str - the {@link String} to be made valid.
    * @return the valid {@link String}
    */
   //In Util stecken
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
    * 
    * @param proof
    * @param path
    * @throws CoreException
    * @throws IOException
    */
   //In Util stecken
   private void saveProof(Proof proof, IPath path) throws CoreException, IOException{ 
      if(proof.name().toString() != null){
         System.out.println(proof.name().toString());
         IFile file = createProofIFile(proof.name().toString(), path);
         if(file != null){
            String filePathAndName = file.getLocation().toOSString();
            // Create proof file content
            // TODO: Refactor functionality to save a Proof into an IFile into a static utility method of KeYUtil#saveProof(Proof proof, IFile) and use this method also in SaveProofHandler
            ProofSaver saver = new ProofSaver(proof, filePathAndName, null);
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            
            String errorMessage = saver.save(out);
            if (errorMessage != null) {
               throw new CoreException(LogUtil.getLogger().createErrorStatus(errorMessage));
            }
            // Save proof file content
            if (file.exists()) {
               file.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
            }
            else {
               file.create(new ByteArrayInputStream(out.toByteArray()), true, null);
            }
         }
      }
   }
   

   private void setMarker(Proof proof, IMethod method) throws CoreException{
      //get File from Method
      IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
      IPath methodPath = method.getPath();
      IFile file = workspaceRoot.getFile(methodPath);
      //set marker
      if(proof.closed()){
         IMarker marker = file.createMarker("org.key_project.key4eclipse.resources.ui.marker.proofClosedMarker");
         if(marker.exists()){
               marker.setAttribute(IMarker.MESSAGE, "Proof closed");
               marker.setAttribute(IMarker.LINE_NUMBER, getLineNumberOfMethod(method, file));
         }
      }
      
      else{
         IMarker marker = file.createMarker("org.key_project.key4eclipse.resources.ui.marker.proofNotClosedMarker");
         if(marker.exists()){
               marker.setAttribute(IMarker.MESSAGE, "Proof not closed");
               marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
               marker.setAttribute(IMarker.LINE_NUMBER, getLineNumberOfMethod(method, file));
         }   
      }
   }

   
   private int getLineNumberOfMethod(IMethod method, IFile file) throws CoreException {
      Position pos = KeYUtil.getCursorPositionForOffset(method, method.getNameRange().getOffset());
      return pos.getLine();
   }

}
