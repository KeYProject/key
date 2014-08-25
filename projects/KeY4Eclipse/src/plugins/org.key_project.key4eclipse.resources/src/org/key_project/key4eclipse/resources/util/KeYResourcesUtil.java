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

package org.key_project.key4eclipse.resources.util;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;

/**
 * @author Stefan Käsdorf
 */
public class KeYResourcesUtil {
   
   public static final String PROOF_FOLDER_NAME = "proofs";
   public static final String PROOF_FILE_EXTENSION = "proof";
   public static final String META_FILE_EXTENSION = "proofmeta";
   
   /**
    * Runs an {@link IncrementalProjectBuilder}s INCREMENTAL_BUILD for the given {@link IProject} and waits for the build to finish.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void cleanBuildProject(final IProject project) throws CoreException{
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      IWorkspaceDescription desc = workspace.getDescription();
      boolean autoBuilding = desc.isAutoBuilding();
      if(autoBuilding){
         try {
            desc.setAutoBuilding(false);
            workspace.setDescription(desc);
            //build
            project.build(IncrementalProjectBuilder.CLEAN_BUILD, new NullProgressMonitor());
         }
         finally {
            desc.setAutoBuilding(autoBuilding);
            workspace.setDescription(desc);
         }
      }
      else{
         //build
         new Job("Converting into KeY project") {

            @Override
            protected IStatus run(IProgressMonitor monitor) {
               try {
                  project.build(IncrementalProjectBuilder.FULL_BUILD, new NullProgressMonitor());
                  return Status.OK_STATUS;
               }
               catch (CoreException e) {
                  return LogUtil.getLogger().createErrorStatus(e);
               }
            }
            
         }.schedule();
      }
   }
   
   
   /**
    * Checks if the given {@link KeYJavaType} is part of the project or an external resource.
    * @param kjt - the {@link KeYJavaType} to use
    * @return false if the {@link KeYJavaType} is an internal resource
    */
   public static boolean filterKeYJavaType(KeYJavaType kjt){
      if (!(kjt.getJavaType() instanceof ClassDeclaration || 
            kjt.getJavaType() instanceof InterfaceDeclaration) || 
            KeYTypeUtil.isLibraryClass(kjt)) {
         return true;
      }
      return false;
   }
   
   
   public static LinkedList<ProofElement> getUsedContractsProofElements(ProofElement pe, List<ProofElement> proofElements){
      LinkedList<ProofElement> usedContracts = new LinkedList<ProofElement>();
      HashSet<IProofReference<?>> proofReferences = pe.getProofReferences();
      if(proofReferences != null && !proofReferences.isEmpty()){
         for(IProofReference<?> proofRef : proofReferences){
            Object target = proofRef.getTarget();
            if(IProofReference.USE_CONTRACT.equals(proofRef.getKind()) && target instanceof Contract){
               Contract contract = (Contract) target;
               for(ProofElement proofElement : proofElements){
                  if(contract.getName().equals(proofElement.getContract().getName())){
                     usedContracts.add(proofElement);
                     break;
                  }
               }
            }
         }
      }
      return usedContracts;
   }
   
   
   public static List<ProofElement> getProofElementsByProofFiles(List<IFile> proofFiles, List<ProofElement> proofElements){
      List<ProofElement> tmpProofElements = cloneList(proofElements);
      List<ProofElement> foundproofElements = new LinkedList<ProofElement>();
      for(IFile proofFile : proofFiles){
         for(ProofElement pe : tmpProofElements){
            if(proofFile.equals(pe.getProofFile())){
               foundproofElements.add(pe);
               tmpProofElements.remove(pe);
               break;
            }
         }
      }
      return foundproofElements;
   }
   
   
   public static <T> List<T> cloneList(List<T> list){
      List<T> clone = new LinkedList<T>();
      for(T t : list){
         clone.add(t);
      }
      return clone;
   }
   
   
   /**
    * Returns a {@link LinkedList} with all Java source folders ais {@link IPath}.
    * @param project - the project to search the source folders for.
    * @return the {@link LinkedList} with the source folders
    */
   public static LinkedList<IPath> getAllJavaSrcFolders(IProject project) {
      LinkedList<IPath> srcFolders = new LinkedList<IPath>();

      IJavaProject javaProject = JavaCore.create(project);
      IClasspathEntry[] classpathEntries;
      try {
         classpathEntries = javaProject.getResolvedClasspath(true);
         for(int i = 0; i<classpathEntries.length;i++){
            IClasspathEntry entry = classpathEntries[i];
            if(entry.getContentKind() == IPackageFragmentRoot.K_SOURCE){
               IPath path = entry.getPath();
               srcFolders.add(path);
            }
         }
      }
      catch (JavaModelException e) {
         srcFolders = new LinkedList<IPath>();
      }
      return srcFolders;
   }

   /**
    * Checks if the given {@link IFolder} is the proof folder of a KeY project.
    * @param element The {@link IFolder} to check.
    * @return {@code true} is proof folder of a KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isProofFolder(IFolder element) throws CoreException {
      return element != null &&
             PROOF_FOLDER_NAME.equals(element.getName()) &&
             element.getParent() instanceof IProject &&
             isKeYProject(element.getProject());
   }
   
   

   
   
   public static int getLineForOffset(String str, int offset){
      StringBuilder sb = new StringBuilder(str);
      int index = 0;
      int lineCount = 0;
      while(index <= offset){
         int indexRN = sb.indexOf("\r\n", index);
         int indexR = sb.indexOf("\r", index);
         int indexN = sb.indexOf("\n", index);
         if(indexRN > -1 && (indexRN <= indexR || indexR == -1) && (indexRN < indexN || indexN == -1)){
            index = indexRN + 2;
         }
         else if(indexR > -1 && (indexR < indexRN || indexRN == -1) && (indexR < indexN || indexN == -1)){
            index = indexR + 1;
         }
         else if(indexN > -1 && (indexN < indexRN || indexRN == -1) && (indexN < indexR || indexR == -1)){
            index = indexN + 1;
         }
         else return 1;
         
         lineCount++;
      }
      return lineCount;
   }
   
   
   /**
    * Checks if the given {@link IProject} is a KeY project.
    * @param project The {@link IProject} to check.
    * @return {@code true} is KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isKeYProject(IProject project) throws CoreException {
      return project != null &&
             project.exists() &&
             project.isOpen() &&
             project.hasNature(KeYProjectNature.NATURE_ID);
   }
   
   public static IProject getProject(IResourceDelta delta){
      IResource res = delta.getResource();
      if(res instanceof IWorkspaceRoot){
         return null;
      }
      else{
         while(!(res instanceof IProject)){
            res = res.getParent();
         }
         return (IProject) res;
      }
   }
   
   public static <T> void mergeLists(List<T> dest, List<T> inserts){
      for(T t : inserts){
         if(!dest.contains(t)){
            dest.add(t);
         }
      }
   }
   
   public static <T> List<T> arrayToList(T[] array){
      List<T> list = new LinkedList<T>();
      for(T t : array){
         list.add(t);
      }
      return list;
   }
   
   /**
    * Creates the folder for the given {@link IFile}
    * @param file - the {@link IFile} to use
    * @return the created {@link IFolder}
    * @throws CoreException
    */
   public static synchronized IFolder createFolder(IFile file) {
      IFolder folder = null;
      IPath folderPath = file.getFullPath().removeLastSegments(1);
      IPath currentFolderPath = new Path(folderPath.segment(0));
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      for(int i = 1; i < folderPath.segmentCount(); i++){
         currentFolderPath = currentFolderPath.append(folderPath.segment(i));
         folder = root.getFolder(currentFolderPath);
         if(!folder.exists()){
            try {
               folder.create(true, true, null);
            }
            catch (CoreException e) {
               if(folder.exists()){
                  createFolder(file);
               }
               else{
                  return null;
               }
            }
         }
      }
      return folder;
   }
   
   
   public static List<ProofElement> getProofElementsForMethod(List<ProofElement> proofElements, IMethod method){
      List<ProofElement> methodProofElements = new LinkedList<ProofElement>();
      if(method != null){
         ICompilationUnit compUnit = method.getCompilationUnit();
         if(compUnit != null){
            try{
               IResource res = compUnit.getResource();
               if(res != null){
                  String src = compUnit.getSource();
                  ISourceRange range = method.getSourceRange();
                  int offset = range.getOffset();
                  int length = range.getLength();
                  int methodStartLine = KeYResourcesUtil.getLineForOffset(src, offset);
                  int methodEndLine = KeYResourcesUtil.getLineForOffset(src, offset+length);
                  for(ProofElement pe : proofElements){
                     IFile peJavaFile = pe.getJavaFile();
                     if(peJavaFile != null && res.equals(peJavaFile)){
                        int sclLine = pe.getSourceLocation().getLineNumber();
                        if(methodStartLine <= sclLine && methodEndLine >= sclLine){
                           methodProofElements.add(pe);
                        }
                     }
                  }
               }
            } catch (JavaModelException e){
               return new LinkedList<ProofElement>();
            }
         }
      }
      return methodProofElements;
   }
   
   
   /**
    * Checks if the given {@link IResource} is a java file and if it is stored in a source folder.
    * @param res - the {@link IResource} to be checked
    * @return true if the given {@link IResource} is a java file and is stored in a source folder.
    */
   public static boolean isJavaFileAndInSrcFolder(IResource res){
      if(IResource.FILE == res.getType() && isInSourceFolder(res)){
         IJavaElement element = JavaCore.create(res);
         if (element instanceof ICompilationUnit) {
            return true;
         }
      }
      return false;
   }
   

   /**
    * Checks if the given {@link IResource} is stored in a source folder.
    * @param res - the {@link IResource} to be checked
    * @param srcFolders - the source folders
    * @return true if the given {@link IResource} is stored in a source folder.
    */
   public static boolean isInSourceFolder(IResource res){
      for(IPath path : KeYResourcesUtil.getAllJavaSrcFolders(res.getProject())){
         if(path.isPrefixOf(res.getFullPath())){
            return true;
         }
      }
      return false;
   }

      
   /**
    * Checks if the given {@link IResource} is a proof or a meta file and if it is stored in the proof folder of the project.
    * @param res - the {@link IResource} to be checked
    * @return true if the given {@link IResource} is a proof or a meta file and if it is stored in the proof folder of the project.
    */
   public static boolean isInProofFolder(IResource res){
      if(IResource.FILE == res.getType()){
         IPath proofFolder = res.getProject().getFullPath().append("proofs");
         return proofFolder.isPrefixOf(res.getFullPath());
      }
      return false;
   }

   /**
    * Returns the proofFolder for the given java{@link IFile}.
    * @param javaFile - the java{@link IFile} to use
    * @return the proof{@link IFolder}
    */
   public static IFolder getProofFolder(IFile javaFile){
      IProject project = javaFile.getProject();
      IFolder mainProofFolder = project.getFolder("proofs");
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
   private static IPath javaToProofPath(IPath path){
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
    * Returns the proof{@link IFile} for the given {@link String} and {@link IPath}.
    * @param name - the name for the {@link IFile}
    * @param path - the {@link IPath} for the {@link IFile} 
    * @return - the {@link IFile} for the Proof
    */
   public static IFile getProofFile(String name, IPath path) {
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
   public static IFile getProofMetaFile(IFile proofFile){
      IPath proofFilePath = proofFile.getFullPath();
      IPath proofMetaFilePath = proofFilePath.removeFileExtension().addFileExtension(KeYResourcesUtil.META_FILE_EXTENSION);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile proofMetaFile = root.getFile(proofMetaFilePath);
      return proofMetaFile;
   }
}