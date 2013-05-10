package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
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

import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

@SuppressWarnings("restriction")
public class KeYProjectBuilder extends IncrementalProjectBuilder {

   private ProofFolderManager folderManager;
   private BackgroundProofer proofer;
   private MarkerManager markerManager;
   private LinkedList<IFile> changedFileList = new LinkedList<IFile>();
   
   
   public KeYProjectBuilder() {
   }

   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IResourceDelta delta = this.getDelta(getProject());
      if (delta != null) {
         if (delta.getKind() == (IResourceDelta.CHANGED)) {
            IProject project = delta.getResource().getProject();
            changedFileList = new LinkedList<IFile>();
            getResourceDelats(delta);
            runProofs(project);
            
         }
      }
      return null;
   }

   
   
   private void getResourceDelats(IResourceDelta delta){
      if(delta.getResource().getType() == IResource.FILE){
         IFile file = (IFile) delta.getResource();
         if(file.getFileExtension().equalsIgnoreCase("java")){
            changedFileList.add(file);
         }
      }
      else{
         IResourceDelta[] deltas = delta.getAffectedChildren(IResourceDelta.CHANGED);
         for(IResourceDelta subDelta : deltas){
            getResourceDelats(subDelta);
         }
      }
   }
   
   
   
   /**
    * Iterates over the given {@link LinkedList<IMethod>}. For each {@link IMethod} the {@link FunctionalOperationContract}s are collected.
    * When a {@link Proof} for the current {@link FunctionalOperationContract} already exists it will be loaded and the AutoMode will be started. If the
    * {@link Proof} doesn't exists it will be instantiated and then the AutoMode will be started. When the AutoMode is done, the {@link Proof} will be
    * saved in a local directory.
    * 
    * @param methods - the {@link LinkedList<IMehod>} with the {@link IMetod}s for which the {@link Proof}s should run.
    * @throws CoreException
    * @throws ProblemLoaderException
    */
   private void runProofs(IProject project) {
      try {  
         
         
         LinkedList<IType> allJavaClasses = collectAllJavaClasses(project);
         LinkedList<IType> changedJavaClasses = collectChangedJavaClasses(project);
         
         
         proofer = new BackgroundProofer(project);
         folderManager = new ProofFolderManager(project);
         markerManager = new MarkerManager();
         
         for(IType type : allJavaClasses){
            IMethod[] methods = type.getMethods();
            LinkedList<IMethod> changedMethods = new LinkedList<IMethod>();
            if(changedJavaClasses.contains(type)){
               markerManager.deleteMarkers(type.getResource());
               
               IMethod[] chngMethods = type.getMethods();
               for(IMethod method : chngMethods){
                  changedMethods.add(method);
               }
            }
            
            for(IMethod method : methods){
               LinkedList<ProofOblInput> proofObls = proofer.createAllProofOblsForMethod(method);
               IPath path = folderManager.getFolderForProofObl(method);
               
               for(ProofOblInput obl : proofObls){
                  IFile file = proofer.getProofIFile(obl.name(), path);
                  folderManager.addToProofList(file);
                 
                  if(!changedMethods.contains(method) && !file.exists()){
                     markerManager.deleteMarkers(method);
                     processProofs(method, obl, file);
                  }
                  else if(changedMethods.contains(method)){
                     processProofs(method, obl, file);
                  }
                  
               }
            }
         }//cleanup the Prooffolder
         folderManager.clean();
      }
      catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
         LogUtil.getLogger().openErrorDialog(null, e);
      }
   }
   
   
   private void processProofs(IMethod method, ProofOblInput obl, IFile file) throws Exception{
      IPath folderPath = folderManager.createFolder(method);
      if (obl != null && !folderPath.isEmpty() && folderPath != null) {
         Proof proof = proofer.createProof(obl, file);
         proofer.saveProof(proof, folderPath);
         markerManager.setMarker(proof, method);
      }
   }

   
   private LinkedList<IType> collectChangedJavaClasses(IProject project) throws JavaModelException {

      LinkedList<IType> changedTypes = new LinkedList<IType>();
      
      for(IFile file : changedFileList){
         ICompilationUnit unit = JavaCore.createCompilationUnitFrom(file);
         IType[] types = unit.getAllTypes();
         for(IType type : types){
            changedTypes.add(type);
            }
         }
      return changedTypes;
   }

   
   private LinkedList<IType> collectAllJavaClasses(IProject project) throws JavaModelException {
      IJavaProject javaProject = JavaCore.create(project);
      IPackageFragment[] packages = javaProject.getPackageFragments();
      LinkedList<IType> classes = new LinkedList<IType>();
      for (IPackageFragment aPackage : packages) {
         if (aPackage.getKind() == IPackageFragmentRoot.K_SOURCE) {

            // find Java Classes
            for (ICompilationUnit unit : aPackage.getCompilationUnits()) {
               IType[] allTypes = unit.getAllTypes();
               for (IType type : allTypes) {
                  classes.add(type);
               }
            }
         }
      }
      
      
      return classes;
   }
}
