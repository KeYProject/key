package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;

import org.eclipse.core.internal.resources.File;
import org.eclipse.core.internal.resources.Folder;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
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

import de.uka.ilkd.key.proof.init.ProofOblInput;

@SuppressWarnings("restriction")
public class ProofFolderManager {

   private IFolder proofFolder = null;
   private LinkedList<IPath> proofFileList = new LinkedList<IPath>();
   
   public ProofFolderManager(IProject project) throws CoreException{
      createProofFolder(project);
   }
   
   public IFolder getProofFolder(){
      return proofFolder;
   }
   
   public LinkedList<IPath> getProofFileList(){
      return proofFileList;
   }
   
   private void createProofFolder(IProject project) throws CoreException{
    //create proofsProofFolder
      IPath projectPath = project.getFullPath();
      IPath proofFolderPath = projectPath.append("Proofs");
      IFolder proofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofFolderPath);
      if(!proofFolder.exists()){
         proofFolder.create(true, true, null);       
      }
      this.proofFolder = proofFolder;
   }
   
   public IPath createFolder(IMethod method) throws CoreException{
      //create proofsPackageFolders
      IPath path = splitPackageString(method.getResource().getFullPath());
      IPath proofPackageFolderPath = proofFolder.getFullPath();
      for(String folderName : path.segments()){
         proofPackageFolderPath = proofPackageFolderPath.append(folderName);
         IFolder proofPackageFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(proofPackageFolderPath);
         if(!proofPackageFolder.exists()){
            proofPackageFolder.create(true, true, null);
         }
      }
      return proofPackageFolderPath;
   }
   
   
   
   private IPath splitPackageString(IPath path){
      IPath folderPath = path;
      while(!folderPath.segment(0).equals("src")){
         folderPath = folderPath.removeFirstSegments(1);
      }
      folderPath = folderPath.removeFirstSegments(1);
      
      return folderPath;
   }
   
   
   
   public void addToProofList(IFile file){
      String filePath = file.getFullPath().toString();
      String proofFolderPath = proofFolder.getFullPath().toString();
      if(filePath.startsWith(proofFolderPath)){
         proofFileList.add(file.getFullPath());
      }
   }
   

   public void clean() throws CoreException{
      if(proofFolder != null){
         deleteFiles(proofFolder);
         deleteFolders(proofFolder);
      }
      proofFileList = null;
   }
   
   
   private void collectAllProofFiles(){
      
   }
   
   private void deleteFiles(IFolder folder) throws CoreException {
      IResource[] members = folder.members();
      for(IResource member : members){
         if(member instanceof File){
            IFile file = (IFile) member;
            IPath path = file.getFullPath();
            if(!proofFileList.contains(path)){
               member.delete(true, null);
            }
            else{
               proofFileList.remove(file);
            }
         }
         else if(member instanceof Folder){
            
            IFolder subFolder = (IFolder) member;
            deleteFiles(subFolder);
         }
      }
   }
   

   private void deleteFolders(IFolder folder) throws CoreException{
      if(folder != null){
         String folderPath = folder.getFullPath().toString();
         if(folderPath.toString().startsWith(proofFolder.getFullPath().toString())){
            if(folder.members().length == 0){
               IContainer parentContainer = folder.getParent();
               folder.delete(true, null);
               if(parentContainer instanceof Folder){
                  IFolder parentFolder = (IFolder) parentContainer;
                  deleteFolders(parentFolder);
               }
            }
            else{
               for(IResource member : folder.members()){
                  if(member instanceof Folder){
                     IFolder subFolder = (IFolder) member;
                     deleteFolders(subFolder);
                  }
               }
               
            }
         }
      }
   }  
   
   
   public IPath getFolderForProofObl(IMethod method){
      IPath path = splitPackageString(method.getResource().getFullPath());
      IPath proofPackageFolderPath = proofFolder.getFullPath();
      for(String folderName : path.segments()){
         proofPackageFolderPath = proofPackageFolderPath.append(folderName);
      }
      return proofPackageFolderPath;
   }

   
   
}
