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

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildJob;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.decorator.ProofFileLightweightLabelDecorator;
import org.key_project.key4eclipse.resources.io.ProofMetaFileAssumption;
import org.key_project.key4eclipse.resources.io.ProofMetaReferencesPrettyPrinter;
import org.key_project.key4eclipse.resources.io.ProofReferenceException;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.util.event.IKeYResourcePropertyListener;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.XMLUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.Pair;

/**
 * @author Stefan Käsdorf
 */
public class KeYResourcesUtil {
   
   public static final String PROOF_FOLDER_NAME = "proofs";
   public static final String PROOF_FILE_EXTENSION = "proof";
   public static final String META_FILE_EXTENSION = "proofmeta";
   public static final String LAST_CHANGES_FILE = ".lastChanges";
   
   /**
    * Key of {@link IResource#getPersistentProperty(QualifiedName)} to store the proof closed result of a proof file.
    */
   public static final QualifiedName PROOF_CLOSED = new QualifiedName("org.key_project.key4eclipse.resources", "closed");
   
   /**
    * Key of {@link IResource#getPersistentProperty(QualifiedName)} to indicate that a proof is in a recursion cycle.
    */
   public static final QualifiedName PROOF_RECURSION_CYCLE = new QualifiedName("org.key_project.key4eclipse.resources", "recursionCycle");
   
   /**
    * All available {@link IKeYResourcePropertyListener}.
    */
   private static List<IKeYResourcePropertyListener> listener = new LinkedList<IKeYResourcePropertyListener>();
   
   /**
    * Runs an {@link IncrementalProjectBuilder}s INCREMENTAL_BUILD for the given {@link IProject} and waits for the build to finish.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void buildProject(IProject project, int buildType) throws CoreException{
      project.build(buildType, new NullProgressMonitor());
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
   
   
   /**
    * Returns the {@link KeYJavaType} for the given {@link IProofReference}.
    * @param proofRef - the {@link IProofReference} to use
    * @return the {@link KeYJavaType}
    * @throws ProofReferenceException 
    */
   public static KeYJavaType getKeYJavaType(IProofReference<?> proofRef) throws ProofReferenceException{
      KeYJavaType kjt = null;
      Object target = proofRef.getTarget();
      if(IProofReference.ACCESS.equals(proofRef.getKind())){
         if(target instanceof IProgramVariable){
            IProgramVariable progVar = (IProgramVariable) target;
            if (progVar instanceof LocationVariable) {
               kjt = ((LocationVariable) progVar).getContainerType();
            }
            else if (progVar instanceof ProgramConstant) {
               kjt = ((ProgramConstant) progVar).getContainerType();
            }
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramVariable");
         }
      }
      else if(IProofReference.CALL_METHOD.equals(proofRef.getKind()) || 
              IProofReference.INLINE_METHOD.equals(proofRef.getKind())){
         if(target instanceof IProgramMethod){
            IProgramMethod progMeth = (IProgramMethod) target;
            kjt = progMeth.getContainerType();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramMethod");
         }
      }
      else if(IProofReference.USE_AXIOM.equals(proofRef.getKind())){
         if(target instanceof ClassAxiom){
            ClassAxiom classAx = (ClassAxiom) target;
            kjt = classAx.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected ClassAxiom");
         }
      }
      else if(IProofReference.USE_CONTRACT.equals(proofRef.getKind())){
         if(target instanceof Contract){
            Contract contract = (Contract) target;
            kjt = contract.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected Contract");
         }
      }
      else if(IProofReference.USE_INVARIANT.equals(proofRef.getKind())){
         if(target instanceof ClassInvariant){
            ClassInvariant classInv = (ClassInvariant) target;
            kjt = classInv.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected ClassInvariant");
         }
      }
      else {
         throw new ProofReferenceException("Unknow proof reference kind found: " + proofRef.getKind());
      }
      return kjt;
   }
   
   //TODO: fix javadoc
   /**
    * Filters a {@link Set} of {@link IProofReference}s in order to exclude external resources. 
    * @param proofReferences {@link Set} of {@link IProofReference}s
    * @return {@link Set} of filtered {@link IProofReference}s 
    */
   public static void filterProofReferences(Set<IProofReference<?>> proofReferences, Set<IProofReference<?>> filteredProofReferences, Set<IProofReference<?>> assumptions) {
      for(IProofReference<?> proofReference : proofReferences){
         try {
            KeYJavaType kjt = getKeYJavaType(proofReference);
            if(!filterKeYJavaType(kjt)){
               filteredProofReferences.add(proofReference);
            }
            else {
               assumptions.add(proofReference);
            }
         }
         catch (ProofReferenceException e) {
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   /**
    * Sorts all elements of a {@link Set} of {@link IProofReference}s by the given {@code sortOrder} and returns a {@link List} with the result.
    * @param proofReferences a {@link Set} of {@link IProofReference}s
    * @param sortOrder the sort order
    * @return a {@link List} with the sorted {@link IProofReference}s
    */
   public static List<IProofReference<?>> sortProofReferences(Set<IProofReference<?>> proofReferences, String... sortOrder) {
      if (proofReferences != null && sortOrder != null && sortOrder.length > 0) {
         List<IProofReference<?>> sortedReferences = new LinkedList<IProofReference<?>>();
         List<IProofReference<?>> axiomList = new LinkedList<IProofReference<?>>();
         List<IProofReference<?>> invList = new LinkedList<IProofReference<?>>();
         List<IProofReference<?>> accessList = new LinkedList<IProofReference<?>>();
         List<IProofReference<?>> callMethodList = new LinkedList<IProofReference<?>>();
         List<IProofReference<?>> inlineMethodList = new LinkedList<IProofReference<?>>();
         List<IProofReference<?>> contractList = new LinkedList<IProofReference<?>>();
         for (IProofReference<?> ref : proofReferences) {
            if (IProofReference.USE_AXIOM.equals(ref.getKind())) {
               axiomList.add(ref);
            }
            else if (IProofReference.USE_INVARIANT.equals(ref.getKind())) {
               invList.add(ref);
            }
            else if (IProofReference.ACCESS.equals(ref.getKind())) {
               accessList.add(ref);
            }
            else if (IProofReference.CALL_METHOD.equals(ref.getKind())) {
               callMethodList.add(ref);
            }
            else if (IProofReference.INLINE_METHOD.equals(ref.getKind())) {
               inlineMethodList.add(ref);
            }
            else if (IProofReference.USE_CONTRACT.equals(ref.getKind())) {
               contractList.add(ref);
            }
         }
         for (String kind : sortOrder) {
            if (IProofReference.USE_AXIOM.equals(kind)) {
               sortedReferences.addAll(axiomList);
               axiomList = new LinkedList<IProofReference<?>>();
            }
            else if (IProofReference.USE_INVARIANT.equals(kind)) {
               sortedReferences.addAll(invList);
               invList = new LinkedList<IProofReference<?>>();
            }
            else if (IProofReference.ACCESS.equals(kind)) {
               sortedReferences.addAll(accessList);
               accessList = new LinkedList<IProofReference<?>>();
            }
            else if (IProofReference.CALL_METHOD.equals(kind)) {
               sortedReferences.addAll(callMethodList);
               callMethodList = new LinkedList<IProofReference<?>>();
            }
            else if (IProofReference.INLINE_METHOD.equals(kind)) {
               sortedReferences.addAll(inlineMethodList);
               inlineMethodList = new LinkedList<IProofReference<?>>();
            }
            else if (IProofReference.USE_CONTRACT.equals(kind)) {
               sortedReferences.addAll(contractList);
               contractList = new LinkedList<IProofReference<?>>();
            }
         }
         sortedReferences.addAll(axiomList);
         sortedReferences.addAll(invList);
         sortedReferences.addAll(accessList);
         sortedReferences.addAll(callMethodList);
         sortedReferences.addAll(inlineMethodList);
         sortedReferences.addAll(contractList);
         return sortedReferences;
      }
      return null;
   }
   
   
   /**
    * Computes the used contracts and called methods.
    * @param pe The {@link ProofElement}.
    * @param proofElements The {@link List} of all available {@link ProofElement}s.
    * @return A {@link Pair} of the used contracts and the called methods.
    */
   public static Pair<List<IFile>, List<String>> computeUsedProofElements(ProofElement pe, HashSet<IProofReference<?>> proofReferences, List<ProofElement> proofElements){
      List<IFile> usedContracts = new LinkedList<IFile>();
      List<String> calledMethods = new LinkedList<String>();
      if(proofReferences != null && !proofReferences.isEmpty()){
         for(IProofReference<?> proofRef : proofReferences){
            Object target = proofRef.getTarget();
            if (IProofReference.USE_CONTRACT.equals(proofRef.getKind()) && target instanceof Contract){
               Contract contract = (Contract) target;
               ImmutableSet<Contract> contracts = proofRef.getSource().getServices().getSpecificationRepository().splitContract(contract);
               for (Contract atomicContract : contracts) {
                  for(ProofElement proofElement : proofElements){
                     if(atomicContract.getName().equals(proofElement.getContract().getName())){
                        usedContracts.add(proofElement.getProofFile());
                        break;
                     }
                  }
               }
            }
            else if (IProofReference.CALL_METHOD.equals(proofRef.getKind())) {
               if (target instanceof IProgramMethod) {
                  IProgramMethod pm = (IProgramMethod) target;
                  String displayName = ClassTree.getDisplayName(pe.getKeYEnvironment().getServices(), pm);
                  calledMethods.add(pm.getContainerType().getFullName() + "#" + displayName);
               }
            }
         }
      }
      return new Pair<List<IFile>, List<String>>(usedContracts, calledMethods);
   }
   
   
   /**
    * Acquires the {@link ProofElement}s associated with the given proof files. 
    * @param proofFiles the given proof files
    * @param proofElements {@link List} of proof elements to check
    * @return a {@link List} of the {@link ProofElement} associated with the given proof files
    */
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
      clone.addAll(list);
      return clone;
   }
   
   
   public static <K,V> Map<K, V> cloneMap(Map<K, V> map){
      Map<K,V> clone = new LinkedHashMap<K, V>();
      clone.putAll(map);
      return clone;
   }
   
   
   public static <T> Set<T> cloneSet(Set<T> set){
      Set<T> clone = new HashSet<T>();
      clone.addAll(set);
      return clone;
   }
   
   
   /**
    * Returns a {@link LinkedList} with all Java source folders ais {@link IPath}.
    * @param project - the project to search the source folders for.
    * @return the {@link LinkedList} with the source folders
    */
   public static IFolder getJavaSrcFolder(IProject project) {
      IJavaProject javaProject = JavaCore.create(project);
      IClasspathEntry[] classpathEntries;
      try {
         classpathEntries = javaProject.getResolvedClasspath(true);
         for(int i = 0; i<classpathEntries.length;i++){
            IClasspathEntry entry = classpathEntries[i];
            if(entry.getContentKind() == IPackageFragmentRoot.K_SOURCE){
               IPath path = entry.getPath();
               return ResourcesPlugin.getWorkspace().getRoot().getFolder(path);
            }
         }
      }
      catch (JavaModelException e) {
         return null;
      }
      return null;
   }

   /**
    * Checks if the given {@link IFolder} is the proof folder of a KeY project.
    * @param element The {@link IFolder} to check.
    * @return {@code true} is proof folder of a KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isProofFolder(IFolder element) {
      return element != null &&
             PROOF_FOLDER_NAME.equals(element.getName()) &&
             element.getParent() instanceof IProject &&
             isKeYProject(element.getProject());
   }
   
   
   /**
    * Checks if the given {@link IProject} is a KeY project.
    * @param project The {@link IProject} to check.
    * @return {@code true} is KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isJavaProject(IProject project) {
      try{
         return project != null &&
                project.exists() &&
                project.isOpen() &&
                project.hasNature(JavaCore.NATURE_ID);
      } catch (CoreException e){
         return false;
      }
   }
   
   
   /**
    * Checks if the given {@link IProject} is a KeY project.
    * @param project The {@link IProject} to check.
    * @return {@code true} is KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isKeYProject(IProject project) {
      try{
         return project != null &&
                project.exists() &&
                project.isOpen() &&
                project.hasNature(KeYProjectNature.NATURE_ID);
      } catch (CoreException e){
         return false;
      }
   }
   
   

   public static <K,V> void mergeMaps(Map<K,V> dest, Map<K,V> inserts){
      for(Map.Entry<K, V> entry : inserts.entrySet()){
         K key = entry.getKey();
         V value = entry.getValue();
         if(!dest.containsKey(key) || (dest.containsKey(key) && dest.get(key) != value)){
            dest.put(key, value);
         }
      }
   }
   

   /**
    * Creates the folder for the given {@link IFile}
    * @param file - the {@link IFile} to use
    * @return the created {@link IFolder}
    * @throws CoreException
    */
   public static IFolder createFolder(IFile file) {
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
   
   
   /**
    * Collects all {@link ProofElement}s associated with a {@link IMethod}
    * @param proofElements {@link List} of all available {@link ProofElement}s
    * @param method the {@link IMethod} to use
    * @return {@link List} with all associated {@link ProofElement}s
    */
   public static List<ProofElement> getProofElementsForMethod(List<ProofElement> proofElements, IMethod method) {
      List<ProofElement> methodProofElements = new LinkedList<ProofElement>();
      if(method != null){
         ICompilationUnit compUnit = method.getCompilationUnit();
         if(compUnit != null){
            try{
               IResource res = compUnit.getResource();
               if(res != null){
                  ISourceRange nameRange = method.getNameRange();
                  Position pos = KeYUtil.getCursorPositionForOffset(compUnit, nameRange.getOffset());
                  for(ProofElement pe : proofElements){
                     IFile peJavaFile = pe.getJavaFile();
                     if(peJavaFile != null && res.equals(peJavaFile) && pe.getSourceLocation().getLineNumber() == pos.getLine()){
                        methodProofElements.add(pe);
                     }
                  }
               }
            } catch (Exception e){
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
      if(isJavaFile(res) && isInSourceFolder(res)){
         return true;
      }
      return false;
   }
   
   
   /**
    * Checks if the given {@link IResource} is a java file.
    * @param res - the {@link IResource} to be checked
    * @return true if the given {@link IResource} is a java file.
    */
   public static boolean isJavaFile(IResource res){
      if(IResource.FILE == res.getType()){
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
      IFolder srcFolder  = KeYResourcesUtil.getJavaSrcFolder(res.getProject());
      if(srcFolder != null && srcFolder.getFullPath().isPrefixOf(res.getFullPath())){
         return true;
      }
      return false;
   }

      
   /**
    * Checks if the given {@link IResource} is a proof or a meta file and if it is stored in the proof folder of the project.
    * @param res - the {@link IResource} to be checked
    * @return true if the given {@link IResource} is a proof or a meta file and if it is stored in the proof folder of the project.
    */
   public static boolean isInProofFolder(IResource res){
      if(IResource.FILE == res.getType() || IResource.FOLDER == res.getType()){
         IPath proofFolder = res.getProject().getFullPath().append("proofs");
         return proofFolder.isPrefixOf(res.getFullPath());
      }
      return false;
   }
   
   
   /**
    * Returns the {@link IProject}'s proof folder
    * @param project the {@link IProject} to use
    * @return the proof folder
    */
   public static IFolder getProofFolder(IProject project){
      if(isKeYProject(project)){
         return project.getFolder(PROOF_FOLDER_NAME);
      }
      return null;
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
         name = IOUtil.validateOSIndependentFileName(name);
         name = name + "." + KeYResourcesUtil.PROOF_FILE_EXTENSION;
         path = path.append(name);
         IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
         return file;
      }
      return null;
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

   /**
    * Returns the {@link IFile} of the {@link Proof} specified by the given {@link IMarker}.
    * @param marker The {@link IMarker}.
    * @return The {@link IFile} of the {@link Proof}.
    * @throws CoreException Occurred Exception
    */
   public static IFile getProofFile(IMarker marker) throws CoreException{
      String str = (String) marker.getAttribute(IMarker.SOURCE_ID);
      if (str != null) {
         IPath proofFilePath = new Path(str);
         IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
         IFile proofFile = root.getFile(proofFilePath);
         return proofFile;
      }
      return null;
   }
   
   /**
    * Defines the persistent property indicating that the proof is closed
    * of the given proof file.
    * @param proofFile The proof file to update its property.
    * @param closed The closed state or {@code null} if unknown.
    * @throws CoreException Occurred Exception.
    */
   public static void setProofClosed(IFile proofFile, Boolean closed) throws CoreException {
      if (proofFile != null && proofFile.exists()) {
         proofFile.setPersistentProperty(PROOF_CLOSED, closed != null ? closed.toString() : null);
         ProofFileLightweightLabelDecorator.redecorateProofFile(proofFile);
         fireProofClosedChanged(proofFile, closed);
      }
   }
   
   /**
    * Checks if the given proof file is closed.
    * @param proofFile The proof file to check.
    * @return The closed state or {@code null} if unknown.
    * @throws CoreException Occurred Exception.
    */
   public static Boolean isProofClosed(IFile proofFile) throws CoreException {
      if (proofFile != null && proofFile.exists()) {
         String property = proofFile.getPersistentProperty(PROOF_CLOSED);
         if (property != null) {
            return Boolean.valueOf(property);
         }
      }
      return false;
   }
   
   /**
    * Defines the persistent property indicating that the proof is part of a recursion cycle
    * of the given proof file.
    * @param proofFile The proof file to update its property.
    * @param inCycle The recursion cycle state or {@code null} if unknown.
    * @throws CoreException Occurred Exception.
    */
   public static void setProofRecursionCycle(IFile proofFile, List<IFile> cycle) throws CoreException {
      if (proofFile != null && proofFile.exists()) {
         String value;
         if (!CollectionUtil.isEmpty(cycle)) {
            StringBuffer sb = new StringBuffer();
            XMLUtil.appendXmlHeader("UTF-8", sb);
            XMLUtil.appendStartTag(0, "list", null, sb);
            for (IFile file : cycle) {
               Map<String, String> attributeValues = Collections.singletonMap("path", file.getFullPath().toString());
               XMLUtil.appendEmptyTag(0, "file", attributeValues, sb);
            }
            XMLUtil.appendEndTag(0, "list", sb);
            value = sb.toString();
         }
         else {
            value = null;
         }
         proofFile.setPersistentProperty(PROOF_RECURSION_CYCLE, value);
         ProofFileLightweightLabelDecorator.redecorateProofFile(proofFile);
         fireProofRecursionCycleChanged(proofFile, cycle);
      }
   }
   
   /**
    * Returns the recursion cycle of the given proof file if available.
    * @param proofFile The proof file to get its recursion cycle.
    * @return The recursion cycle or {@code null} if not part of a cycle.
    * @throws CoreException Occurred Exception.
    */
   public static List<IFile> getProofRecursionCycle(IFile proofFile) throws CoreException {
      if (proofFile != null && proofFile.exists()) {
         String property = proofFile.getPersistentProperty(PROOF_RECURSION_CYCLE);
         if (property != null) {
            try {
               final List<IFile> cycle = new LinkedList<IFile>();
               SAXParserFactory factory = SAXParserFactory.newInstance();
               factory.setNamespaceAware(true);
               SAXParser saxParser = factory.newSAXParser();
               saxParser.parse(new ByteArrayInputStream(property.getBytes()), new DefaultHandler() {
                  @Override
                  public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
                     if ("file".equals(qName)) {
                        String path = attributes.getValue("path");
                        if (path != null) {
                           cycle.add(ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path)));
                        }
                     }
                  }
               });
               return cycle;
            }
            catch (Exception e) {
               throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
            }
         }
      }
      return null;
   }
   
   /**
    * Adds the given {@link IKeYResourcePropertyListener}.
    * @param l The {@link IKeYResourcePropertyListener} to add.
    */
   public static void addKeYResourcePropertyListener(IKeYResourcePropertyListener l) {
      if (l != null) {
         listener.add(l);
      }
   }
   
   /**
    * Removes the given {@link IKeYResourcePropertyListener}.
    * @param l The {@link IKeYResourcePropertyListener} to remove.
    */
   public static void removeKeYResourcePropertyListener(IKeYResourcePropertyListener l) {
      if (l != null) {
         listener.remove(l);
      }
   }
   
   /**
    * Returns all available {@link IKeYResourcePropertyListener}.
    * @return The available {@link IKeYResourcePropertyListener}.
    */
   public static IKeYResourcePropertyListener[] getKeYResourcePropertyListeners() {
      return listener.toArray(new IKeYResourcePropertyListener[listener.size()]);
   }

   /**
    * Fires the event {@link IKeYResourcePropertyListener#proofClosedChanged(IFile, Boolean)} to all listener.
    * @param proofFile The changed proof file.
    * @param closed The new closed state.
    */
   protected static void fireProofClosedChanged(IFile proofFile, Boolean closed) {
      IKeYResourcePropertyListener[] toInform = getKeYResourcePropertyListeners();
      for (IKeYResourcePropertyListener l : toInform) {
         l.proofClosedChanged(proofFile, closed);
      }
   }
   
   /**
    * Fires the event {@link IKeYResourcePropertyListener#proofRecursionCycleChanged(IFile, List)} to all listener.
    * @param proofFile The changed proof file.
    * @param cycle The new recursion cycle or {@code null} if not part of a cycle.
    */
   protected static void fireProofRecursionCycleChanged(IFile proofFile, List<IFile> cycle) {
      IKeYResourcePropertyListener[] toInform = getKeYResourcePropertyListeners();
      for (IKeYResourcePropertyListener l : toInform) {
         l.proofRecursionCycleChanged(proofFile, cycle);
      }
   }
   
   
//   public static List<Job> getProjectWorkspaceBuildJobs(IProject project){
//      
//   }
   
   
   /**
    * Collects all currently living {@link KeYProjectBuildJob}s of a particular {@link IProject}
    * @param project the {@link IProject} to use
    * @return {@link List} with all {@link KeYProjectBuildJob}s
    */
   public static List<KeYProjectBuildJob> getProjectBuildJobs(IProject project){
      List<KeYProjectBuildJob> projectKeYJobs = new LinkedList<KeYProjectBuildJob>();
      if(project != null){
         IJobManager jobMan = Job.getJobManager();
         Job[] jobs = jobMan.find(KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB);
         for(Job job : jobs){
            if(job instanceof KeYProjectBuildJob){
               KeYProjectBuildJob keyJob = (KeYProjectBuildJob) job;
               if(project.equals(keyJob.getProject())){
                  projectKeYJobs.add(keyJob);
               }
            }
         }
      }
      return projectKeYJobs;
   }

   
   /**
    * Checks if the given {@link IResource} is a proof file
    * @param res the {@link IResource} to use 
    * @return true if the {@link IResource} is a proof file. Otherwise false 
    */
   public static boolean isProofFile(IResource res){
      if(res != null && res.exists()){
         return KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(res.getFileExtension());
      }
      return false;
   }
   
   /**
    * Checks if the given {@link IResource} is a meta file
    * @param res the {@link IResource} to use 
    * @return true if the {@link IResource} is a meta file. Otherwise false 
    */
   public static boolean isMetaFile(IResource res){
      if(res != null && res.exists()){
         return KeYResourcesUtil.META_FILE_EXTENSION.equals(res.getFileExtension());
      }
      return false;
   }
   
   
   /**
    * Checks if the given {@link IResource} is a proof file and if it is located in the {@link IProject}'s proof folder
    * @param res the {@link IResource} to use 
    * @return true if the {@link IResource} is a proof file in the proof folder. Otherwise false 
    */
   public static boolean isProofFileAndInProofFolder(IResource res){
      if(res != null && res.exists() && isProofFile(res)){
         IProject project = res.getProject();
         if(KeYResourcesUtil.isKeYProject(project) && isInProofFolder(res)){
            return true;
         }
      }
      return false;
   }
   
   /**
    * Checks if the given {@link IFile} is the {@link IProject}s lastChangesFile
    * @param file the IFile to check
    * @return true if the {@link IFile} is the lastChangesFile. Otherwise false
    */
   public static boolean isLastChangesFile(IFile file) {
      if (file != null) {
         return LAST_CHANGES_FILE.equals(file.getName()) &&
                file.getParent() instanceof IFolder &&
                KeYResourcesUtil.isProofFolder((IFolder)file.getParent());
      }
      return false;
   }
   

   /**
    * Synchronizes the given {@link IProject}
    * @param project the {@link IProject} to use
    */
   public static void synchronizeProject(IProject project){
      if(!project.isSynchronized(IResource.DEPTH_INFINITE)){
         try {
            project.refreshLocal(IResource.DEPTH_INFINITE, null);
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   
   /**
    * Converts a {@link ImmutableArray} of {@link ParameterDeclaration}s into a semicolon separated {@link String}
    * @param parameters {@link ImmutableArray} of {@link ParameterDeclaration}s 
    * @return the converted Array
    */
   public static String parametersToString(ImmutableArray<ParameterDeclaration> parameters){
      String parameterString = "";
      for(ParameterDeclaration parameter : parameters){
         parameterString += parameter.getTypeReference().getName() + ";";
      }
      return parameterString;
   }
   

   /**
    * Removes all line breaks in a {@link String}
    * @param str the {@link String} to use
    * @return {@link String} without line breaks
    */
   private static String removeLineBreaks(String str){
      str = str.replaceAll("\r\n", " ");
      str = str.replaceAll("\r", " ");
      str = str.replaceAll("\n", " ");
      return str;
   }

   /**
    * Removes all tabs in a {@link String} and replaces them with a single space
    * @param str the {@link String} to use
    * @return {@link String} without tabs
    */
   private static String removeTabs(String str){
      str = str.replaceAll("\t", " ");
      return str;
   }

   /**
    * Removes all multiple spaces and replaces them with a single space
    * @param str the {@link String} to use
    * @return {@link String} without tabs
    */
   private static String removeMultiSpaces(String str){
      String[] splits = str.split(" ");
      String trimmed = "";
      for(String split : splits) {
         trimmed += split + " ";
      }
      return trimmed.trim();
   }
   
   
   /**
    * Creates a single line {@link String} representation of the source code of a {@link MethodDeclaration}
    * @param methodDecl the {@link MethodDeclaration} to use
    * @return the source {@link String}
    */
   public static String createSourceString(MethodDeclaration methodDecl){
      StringWriter sw = new StringWriter();
      try{
         ProofMetaReferencesPrettyPrinter pp = new ProofMetaReferencesPrettyPrinter(sw, true);
         pp.printInlineMethodDeclaration(methodDecl);
      }
      catch (IOException e){
         LogUtil.getLogger().logError(e);
      }
      String src = sw.toString();
      src = KeYResourcesUtil.removeLineBreaks(src);
      src = KeYResourcesUtil.removeTabs(src);
      src = KeYResourcesUtil.removeMultiSpaces(src);
      return src;
   }
   
   
   /**
    * Searches a {@link KeYJavaType} for a {@link IProgramMethod} with the given name and parameters
    * @param kjt the {@link KeYJavaType} to use
    * @param method the method name
    * @param parameters semicolon separated parameters
    * @return the {@link IProgramMethod} of null
    */
   public static IProgramMethod getMethodForKjt(KeYJavaType kjt, String method, String parameters) {
      if(kjt != null && kjt.getJavaType() instanceof TypeDeclaration) {
         TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
         for(MemberDeclaration memberDecl : typeDecl.getMembers()) {
            if (memberDecl instanceof IProgramMethod) {
               IProgramMethod pm = (IProgramMethod) memberDecl;
               MethodDeclaration md = pm.getMethodDeclaration();
               if (md.getName().equals(method) && KeYResourcesUtil.parametersToString(md.getParameters()).equals(parameters)) {
                  return pm;
               }
            }
         }
      }
      return null;
   }
   
   
   /**
    * Collects each implementation of the method specified by {@code methodName} and {@code parameters} in the given {@link KeYJavaType} and all subTypes. 
    * @param env the {@link KeYEnvironment} to use
    * @param kjt the {@link KeYJavaType} to use
    * @param methodName the method name
    * @param parameters semicolon separated parameters
    * @return {@link Map} with each {@link KeYJavaType} mapping to the associated {@link IProgramMethod}
    */
   public static List<Pair<KeYJavaType, IProgramMethod>> getKjtsOfAllImplementations(KeYEnvironment<?> env, KeYJavaType kjt, String methodName, String parameters) {
      List<Pair<KeYJavaType, IProgramMethod>> types = new LinkedList<Pair<KeYJavaType, IProgramMethod>>();
      IProgramMethod pm = KeYResourcesUtil.getMethodForKjt(kjt, methodName, parameters);
      if(pm != null) {
         types.add(new Pair<KeYJavaType, IProgramMethod>(kjt, pm));
      }
      ImmutableList<KeYJavaType> subTypes = env.getJavaInfo().getAllSubtypes(kjt);
      Iterator<KeYJavaType> it = subTypes.iterator();
      while(it.hasNext()){
         kjt = it.next();
         if((pm = KeYResourcesUtil.getMethodForKjt(kjt, methodName, parameters)) != null){
            types.add(new Pair<KeYJavaType, IProgramMethod>(kjt, pm));
         }
      }
      return types;
   }
   
   
   /**
    * Creates a semicolon separated {@link String} of all {@link KeYJavaType} keys in the given {@link Map}
    * @param implementations the {@link Map} to use
    * @return semicolon separated {@link String} of all {@link KeYJavaType}s
    */
   public static String implementationTypesToString(List<Pair<KeYJavaType, IProgramMethod>> implementations) {
      String implementationTypesString = "";
      for(Pair<KeYJavaType, IProgramMethod> pair : implementations){
         if(implementationTypesString != null){
            implementationTypesString += pair.first.getFullName() + ";";
         }
      }
      return implementationTypesString;
   }

   
   /**
    * Returns the {@link FieldDeclaration} matching the given name in the given {@link KeYJavaType}
    * @param kjt the {@link KeYJavaType} to use
    * @param name the field name
    * @return the {@link FieldDeclaration} or null
    */
   public static FieldDeclaration getFieldDeclFromKjt(KeYJavaType kjt, String name) {
      if(kjt.getJavaType() instanceof TypeDeclaration) {
         TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
         for(MemberDeclaration memberDecl : typeDecl.getMembers()){
            if(memberDecl instanceof FieldDeclaration){
               FieldDeclaration fieldDecl = (FieldDeclaration) memberDecl;
               ImmutableArray<FieldSpecification> fieldSpecs = fieldDecl.getFieldSpecifications();
               if(fieldSpecs.size() == 1){
                  FieldSpecification fieldSpec = fieldSpecs.get(0);
                  if(fieldSpec.getName().equals(name)){
                     return fieldDecl;
                  }
               }
            }
         }
      }
      return null;
   }

   
   /**
    * Converts the given {@link Contract} into a {@link String} representation
    * @param contract the {@link Contract} to use
    * @return the {@link String} representation
    */
   public static String contractToString(Contract contract) {
      return contract.toString();
   }
   

   /**
    * Converts the given {@link RepresentsAxiom} into a {@link String} representation
    * @param axiom the {@link RepresentsAxiom} to use
    * @return the {@link String} representation
    */
   public static String repAxiomToString(RepresentsAxiom axiom) {
      return axiom.toString();
   }


   /**
    * Converts the given {@link ClassInvariant} into a {@link String} representation
    * @param invariant the {@link ClassInvariant} to use
    * @return the {@link String} representation
    */
   public static String invariantToString(ClassInvariant invariant){
      return invariant.getOriginalInv().toString();
   }


   public static List<ProofMetaFileAssumption> computeProofMetaFileAssumtionList(Services services, Set<IProofReference<?>> assumptions) {
      List<ProofMetaFileAssumption> assumptionList = new LinkedList<ProofMetaFileAssumption>();
      for (IProofReference<?> proofRef : assumptions) {
         String kind = null;
         String name = null;
         String targetStr = null;
         String type = null;
         Object target = proofRef.getTarget();
         if(IProofReference.USE_AXIOM.equals(proofRef.getKind())){
            if(target instanceof ClassAxiom){
               ClassAxiom classAx = (ClassAxiom) target;
               kind = proofRef.getKind();
               name = classAx.getDisplayName();
               targetStr = ClassTree.getDisplayName(services, classAx.getTarget());
               type = classAx.getKJT().getFullName();
            }
         }
         else if(IProofReference.USE_CONTRACT.equals(proofRef.getKind())){
            if(target instanceof Contract){
               Contract contract = (Contract) target;
               kind = proofRef.getKind();
               name = contract.getDisplayName();
               targetStr = ClassTree.getDisplayName(services, contract.getTarget());
               type = contract.getKJT().getFullName();
            }
         }
         else if(IProofReference.USE_INVARIANT.equals(proofRef.getKind())){
            if(target instanceof ClassInvariant){
               ClassInvariant classInv = (ClassInvariant) target;
               kind = proofRef.getKind();
               name = classInv.getDisplayName();
               type = classInv.getKJT().getFullName();
            }
         }
         if(kind != null){
            assumptionList.add(new ProofMetaFileAssumption(kind, name, targetStr, type));
         }
      }
      return assumptionList;
   }

   public static String getJavaFilePackage(IFile file){
      IJavaElement je = JavaCore.create(file);
      if(je != null) {
         if(je instanceof ICompilationUnit) {
            ICompilationUnit cu = (ICompilationUnit) je;
            IJavaElement parent = cu.getParent();
            if(parent instanceof IPackageFragment) {
               IPackageFragment pf = (IPackageFragment) parent;
               return pf.getElementName();
            }
         }
      }
      return null;
   }
}