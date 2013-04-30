package org.key_project.key4eclipse.resources;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
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
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.keyide.ui.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
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



public class KeYProjectBuilder extends IncrementalProjectBuilder {

   public KeYProjectBuilder() {
   }

   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IResourceDelta delta = this.getDelta(getProject());
      if(delta != null){
         if(delta.getKind() == (IResourceDelta.CHANGED)){
            LinkedList<IMethod> methods = collectAllMethods(delta);
            for(IMethod meth : methods){
               System.out.println(meth.getElementName());
            }
            
            if(!methods.isEmpty()){
               runProofs(methods);
            }
            else{
               System.out.println("No methods found in this Project");
            }
         }
      }
      return null;
   }
   
   
   
   
   private LinkedList<IMethod> collectAllMethods(IResourceDelta delta) throws JavaModelException{
      IProject project = delta.getResource().getProject();
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
   
   private void runProofs(LinkedList<IMethod> methods){
      for(IMethod method : methods){
         try{
            //Initialize KeYEnvironment for this method
            IProject project = method.getResource().getProject();
            final File location = ResourceUtil.getLocation(project);
            final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
            final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
            
            KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(location, classPaths, bootClassPath);
            
            ImmutableSet<FunctionalOperationContract> operationContracts = searchContractsForMethod(method, environment);
            
            
            //Create Folder for Proofs of this Method
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
               if(!file.exists()){
                  System.out.println("NEW PROOF");
                  Proof proof = environment.createProof(input);
                  System.out.println("Proof: " + proof.name());
                  environment.getUi().startAndWaitForAutoMode(proof);
                  saveProofToProofFolder(proof, folderPath);
               }
               else{
                  System.out.println("PROOF EXISTS");
                  final File proofFile = file.getLocation().toFile();
                  KeYFile keyFile = new KeYFile(null,  proofFile, null);
                  try{
                     @SuppressWarnings("unused")
                     String javaPath = keyFile.readJavaPath();
                     final File keyFileBoot = keyFile.readBootClassPath();
                     final List<File> keyFileClassPaths = keyFile.readClassPath();
                     environment = KeYEnvironment.load(proofFile, keyFileClassPaths, keyFileBoot);
                     Proof proof = environment.getLoadedProof();
                     System.out.println("Proof: " + proof.name());
                     if(!proof.closed()){
                        environment.getUi().startAndWaitForAutoMode(proof);
                     saveProofToProofFolder(proof, folderPath);
                     }
                  }
                  catch (ProofInputException e) {
                     LogUtil.getLogger().createErrorStatus(e);
                  }
               }
            }
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
         }
      }      
   }
   
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
   
   private IPath createProofFolder(IMethod method) throws CoreException{
      IPath projectPath = method.getJavaProject().getPath();
      IPath proofMainFolderPath = projectPath.append("Proofs");
      IFolder proofMainFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofMainFolderPath);
      if(!proofMainFolder.exists()){
         proofMainFolder.create(true, true, null);
      }
      IPath proofClassFolderPath = proofMainFolderPath.append(method.getParent().getElementName());
      IFolder proofClassFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofClassFolderPath);
      //TODO: Create überprüfen. Beide parameter true?
      if(!proofClassFolder.exists()){
         proofClassFolder.create(true, true, null);
      }
      return proofClassFolderPath;
   }
   
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
   
   private void saveProofToProofFolder(Proof proof, IPath path) throws CoreException, IOException{ 
      if(proof.name().toString() != null){
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
   
   public ImmutableSet<FunctionalOperationContract> searchContractsForMethod(IMethod method, KeYEnvironment<CustomConsoleUserInterface> environment) throws ProofInputException {
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

}
