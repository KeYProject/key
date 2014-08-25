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
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
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
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.decorator.ProofFileLightweightLabelDecorator;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.event.IKeYResourcePropertyListener;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.XMLUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.proof.Proof;
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
   public static void cleanBuildProject(final IProject project) throws CoreException {
      IWorkspace workspace = ResourcesPlugin.getWorkspace();
      IWorkspaceDescription desc = workspace.getDescription();
      boolean autoBuilding = desc.isAutoBuilding();
      if (autoBuilding) {
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
      else {
         //build
         new Job("Converting into KeY Project") {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               try {
                  project.build(IncrementalProjectBuilder.CLEAN_BUILD, monitor);
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
    * Collects all meta{@link IFile}s in the given {@link IFolder} and all subfolders.
    * @param folder - the {@link IFolder} to use
    * @return a {@link LinkedList} with all meta{@link IFile}s
    * @throws CoreException
    */
   private static LinkedList<IFile> collectAllMetaFiles(IFolder folder) throws CoreException{
      MetaFileVisitor mfv = new MetaFileVisitor();
      folder.accept(mfv, IResource.DEPTH_INFINITE, IContainer.INCLUDE_HIDDEN);
      return mfv.getMetaFileList();
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
   
   
   public static LinkedList<ProofElement> getUsedContractsProofElements(ProofElement pe, LinkedList<ProofElement> proofElements){
      LinkedList<ProofElement> usedContracts = new LinkedList<ProofElement>();
      LinkedHashSet<IProofReference<?>> proofReferences = pe.getProofReferences();
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
   
   
   public static LinkedList<ProofElement> getProofElementsByProofFiles(LinkedList<IFile> proofFiles, LinkedList<ProofElement> proofElements){
      LinkedList<ProofElement> tmpProofElements = cloneLinkedList(proofElements);
      LinkedList<ProofElement> foundproofElements = new LinkedList<ProofElement>();
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
   
   
   /**
    * Clones the given {@link LinkedList} of {@link ProofElement}s.
    * @param proofElements - the {@link LinkedList} to clone
    * @return the cloned {@link LinkedList}
    */
   public static LinkedList<ProofElement> cloneLinkedList(LinkedList<ProofElement> proofElements){
      LinkedList<ProofElement> clone = new LinkedList<ProofElement>();
      for(ProofElement pe : proofElements){
         clone.add(pe);
      }
      return clone;
   }
   
   
   /**
    * Applies the {@link KeYProjectProperties#PROP_HIDE_META_FILES} to all metaFiles in the given {@link IProject}.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    */
   public static void hideMetaFiles(IProject project) throws CoreException{
      boolean hide = KeYProjectProperties.isHideMetaFiles(project);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IPath proofFolderPath = project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFolder proofFolder = root.getFolder(proofFolderPath);
      if(proofFolder.exists()){
         LinkedList<IFile> metaFiles = collectAllMetaFiles(proofFolder);
         for(IFile metaFile : metaFiles){
            metaFile.setHidden(hide);
            metaFile.refreshLocal(IResource.DEPTH_ZERO, null);
         }
      }
      project.refreshLocal(IResource.DEPTH_INFINITE, null);
   }
   
   
   /**
    * Returns a {@link LinkedList} with all Java source folders ais {@link IPath}.
    * @param project - the project to search the source folders for.
    * @return the {@link LinkedList} with the source folders.
    * @throws JavaModelException
    */
   public static LinkedList<IPath> getAllJavaSrcFolders(IProject project) throws JavaModelException{
      LinkedList<IPath> srcFolders = new LinkedList<IPath>();

      IJavaProject javaProject = JavaCore.create(project);
      IClasspathEntry[] classpathEntries = javaProject.getResolvedClasspath(true);
      
      for(int i = 0; i<classpathEntries.length;i++){
         IClasspathEntry entry = classpathEntries[i];
         if(entry.getContentKind() == IPackageFragmentRoot.K_SOURCE){
            IPath path = entry.getPath();
            srcFolders.add(path);
         }
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
   
   /**
    * Checks if the given {@link IProject} is a KeY project.
    * @param project The {@link IProject} to check.
    * @return {@code true} is KeY project, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public static boolean isKeYProject(IProject project) throws CoreException {
      return project != null &&
             project.isOpen() &&
             project.hasNature(KeYProjectNature.NATURE_ID);
   }
   
   /**
    * Returns the {@link IFile} of the {@link Proof} specified by the given {@link IMarker}.
    * @param marker The {@link IMarker}.
    * @return The {@link IFile} of the {@link Proof}.
    * @throws CoreException Occurred Exception
    */
   public static IFile getProofFile(IMarker marker) throws CoreException{
      String str = (String) marker.getAttribute(IMarker.SOURCE_ID);
      IPath proofFilePath = new Path(str);
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile proofFile = root.getFile(proofFilePath);
      return proofFile;
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
         else {
            return null;
         }
      }
      else {
         return null;
      }
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
         else {
            return null;
         }
      }
      else {
         return null;
      }
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
}