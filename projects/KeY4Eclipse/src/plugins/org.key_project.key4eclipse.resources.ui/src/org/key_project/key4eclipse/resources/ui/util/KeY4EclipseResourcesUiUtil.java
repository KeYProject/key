package org.key_project.key4eclipse.resources.ui.util;

import java.util.LinkedList;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

public class KeY4EclipseResourcesUiUtil {

   public static void hideMetaFiles(IProject project, boolean hide) throws CoreException{
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath proofFolderPath = project.getFullPath().append("Proofs");
      IFolder proofFolder = root.getFolder(proofFolderPath);
      if(proofFolder.exists()){
         LinkedList<IFile> metaFiles = collectAllMetaFiles(proofFolder);
         for(IFile metaFile : metaFiles){
            metaFile.setHidden(hide);
            //TODO: refresh gui
            metaFile.refreshLocal(IResource.DEPTH_ZERO, null);
         }
      }
   }

   
   private static LinkedList<IFile> collectAllMetaFiles(IFolder folder) throws CoreException{
      LinkedList<IFile> metaFileList = new LinkedList<IFile>();
      IResource[] members = folder.members(IContainer.INCLUDE_HIDDEN);
      for(IResource member : members){
         if(member.getType() == IResource.FILE){
            IFile file = (IFile) member;
            if(file.getFileExtension().equalsIgnoreCase("meta")){
               metaFileList.add(file);
            }
         }
         else if(member.getType() == IResource.FOLDER){
            IFolder subFolder = (IFolder) member;
            metaFileList.addAll(collectAllMetaFiles(subFolder));
         }
      }
      return metaFileList;
   }
}
