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
import java.util.Collections;
import java.util.HashSet;
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
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildJob;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.decorator.ProofFileLightweightLabelDecorator;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.util.event.IKeYResourcePropertyListener;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.XMLUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.Contract;
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
    * Computes the used contracts and called methods.
    * @param pe The {@link ProofElement}.
    * @param proofElements The {@link List} of all available {@link ProofElement}s.
    * @return A {@link Pair} of the used contracts and the called methods.
    */
   public static Pair<List<IFile>, List<String>> computeUsedProofElements(ProofElement pe, List<ProofElement> proofElements){
      List<IFile> usedContracts = new LinkedList<IFile>();
      List<String> calledMethods = new LinkedList<String>();
      HashSet<IProofReference<?>> proofReferences = pe.getProofReferences();
      if(proofReferences != null && !proofReferences.isEmpty()){
         for(IProofReference<?> proofRef : proofReferences){
            Object target = proofRef.getTarget();
            if (IProofReference.USE_CONTRACT.equals(proofRef.getKind()) && target instanceof Contract){
               Contract contract = (Contract) target;
               ImmutableSet<Contract> contracts = pe.getSpecificationRepository().splitContract(contract);
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
   public static boolean isProofFolder(IFolder element) {
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
   
   
   public static <T> void mergeLists(List<T> dest, List<T> inserts){ // TODO: Move to CollectionUtil
      for(T t : inserts){
         if(!dest.contains(t)){
            dest.add(t);
         }
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
   
   
   public static <T> List<T> arrayToList(T[] array){ // TODO: Move to CollectionUtil
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
      if(IResource.FILE == res.getType() || IResource.FOLDER == res.getType()){
         IPath proofFolder = res.getProject().getFullPath().append("proofs");
         return proofFolder.isPrefixOf(res.getFullPath());
      }
      return false;
   }
   
   
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
         name = ResourceUtil.validateWorkspaceFileName(name);
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
   
   
   public static int getNumberOfAutoBuildsInQueue(IProject project){
      int num = 0;
      List<KeYProjectBuildJob> projectBuildJobs = KeYResourcesUtil.getProjectBuildJobs(project);
      for(KeYProjectBuildJob job : projectBuildJobs){
         if(KeYProjectBuildJob.AUTO_BUILD == job.getBuildType() && Job.WAITING == job.getState()){
            num++;
         }
      }
      return num;
   }
   
   
   public static boolean isProofFile(IFile file){
      if(file != null && file.exists()){
         IProject project = file.getProject();
         if(KeYResourcesUtil.isKeYProject(project) && isInProofFolder(file) && KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(file.getFileExtension())){
            return true;
         }
      }
      return false;
   }
   
   
   public static List<IFile> getAllProofFiles(IResource res){
      if(res != null && res.exists()){
         if(res.getType() == IResource.PROJECT){
            IProject project = (IProject) res;
            if(KeYResourcesUtil.isKeYProject(project)){
               return getAllProofFiles(project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME));
            }
         }
         else if(res.getType() == IResource.FOLDER){
            IFolder folder = (IFolder) res;
            if(KeYResourcesUtil.isKeYProject(folder.getProject()) && KeYResourcesUtil.isInProofFolder(folder)){
               try{
                  List<IFile> files = new LinkedList<IFile>();
                  for(IResource subRes : folder.members()){
                     files.addAll(KeYResourcesUtil.getAllProofFiles(subRes));
                  }
                  return files;
               }
               catch(CoreException e){
                  LogUtil.getLogger().logError(e);
               }
            }
         }
         else if(res.getType() == IResource.FILE){
            IFile file = (IFile) res;
            if(KeYResourcesUtil.isKeYProject(file.getProject()) && KeYResourcesUtil.isInProofFolder(file) && KeYResourcesUtil.isProofFile(file)){
               List<IFile> files = new LinkedList<IFile>();
               files.add(file);
               return files;
            }
         }
      }
      return new LinkedList<IFile>();
   }
   

   public static boolean isLastChangesFile(IFile file) {
      if (file != null) {
         return LAST_CHANGES_FILE.equals(file.getName()) &&
                file.getParent() instanceof IFolder &&
                KeYResourcesUtil.isProofFolder((IFolder)file.getParent());
      }
      return false;
   }
   
   
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
}