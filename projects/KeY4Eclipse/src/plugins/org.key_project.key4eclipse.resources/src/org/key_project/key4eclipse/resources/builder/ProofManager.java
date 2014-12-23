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

package org.key_project.key4eclipse.resources.builder;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.io.LastChangesFileWriter;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileTypeElement;
import org.key_project.key4eclipse.resources.io.ProofMetaFileWriter;
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.marker.MarkerUtil;
import org.key_project.key4eclipse.resources.projectinfo.AbstractContractContainer;
import org.key_project.key4eclipse.resources.projectinfo.AbstractTypeContainer;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo;
import org.key_project.key4eclipse.resources.projectinfo.ContractInfo.ContractModality;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.ObserverFunctionInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.EditorSelection;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.util.Pair;

/**
 * The ProofManager is responsible for the maintasks during the build. It runs and saves the 
 * proofs, creates marker, initializes threads and manages the folderstructure.
 * @author Stefan Käsdorf
 */
public class ProofManager {

   private final IProject project;
   private int buildType;
   private final IFolder mainProofFolder;
   private List<ProofElement> proofElements;
   private KeYProjectDelta keyDelta;
   private Set<IFile> changedJavaFiles;
   private EditorSelection editorSelection;
   private final KeYEnvironment<CustomUserInterface> environment;
   private List<ProofElement> proofQueue = Collections.synchronizedList(new LinkedList<ProofElement>());
   public static final List<Pair<ProofElement, InputStream>> proofsToSave = Collections.synchronizedList(new LinkedList<Pair<ProofElement, InputStream>>());

   
   /**
    * The Constructor that loads the {@link KeYEnvironment}. If that fails the problemLoaderException will be set.
    * @param project - the {@link IProject} to use
    * @throws CoreException
    * @throws ProblemLoaderException 
    */
   public ProofManager(IProject project, int buildType, EditorSelection editorSelection) throws CoreException, ProblemLoaderException{
      this.project = project;
      this.buildType = buildType;
      this.mainProofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME));
      this.keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
      this.editorSelection = editorSelection;
      try {
         File location = KeYResourceProperties.getSourceClassPathLocation(project);
         File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
         List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
         environment = KeYEnvironment.load(location, classPaths, bootClassPath);
      }
      catch (ProblemLoaderException e) {
         handleProblemLoaderException(e);
         throw e;
      }
      MarkerUtil.deleteKeYMarkerByType(project, IResource.DEPTH_INFINITE, MarkerUtil.PROBLEMLOADEREXCEPTIONMARKER_ID); 
   }
   
   
   /**
    * Disposes this {@link ProofManager}.
    */
   public void dispose() {
      if (environment != null) {
         environment.dispose();
      }
   }
   
   
   /**
    * Handles the occurrence of a {@link ProblemLoaderException}. All KeYMarker will be deleted and a ProblemException{@link IMarker} will be set.
    * @param e - the {@link ProblemLoaderException}
    * @throws CoreException
    */
   private void handleProblemLoaderException(ProblemLoaderException e) throws CoreException{
      IResource res = project;
      int lineNumber = -1;
      if(e.getOrigin() != null && e.getOrigin().getFile() != null){
         String originPath = e.getOrigin().getFile().getAbsolutePath();
         StringBuffer sb = new StringBuffer(e.getMessage());
         int indexOfOriginPath = sb.indexOf(originPath);
         if(indexOfOriginPath != -1){
            sb.delete(0, indexOfOriginPath);
            StringBuffer tmpSb = new StringBuffer(sb.toString().toLowerCase(Locale.US));
            int indexOfOriginPathEnd = tmpSb.indexOf(".java") + 5;
            if(indexOfOriginPathEnd != -1){
               String errorFilePath = sb.substring(0, indexOfOriginPathEnd);
               IFile file = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(new Path(errorFilePath));
               if(file != null && file.exists()){
                  sb.delete(0, indexOfOriginPathEnd);
                  int indexOfLine = sb.indexOf("line ");
                  int indexOfColumn = sb.indexOf(", column");
                  if(indexOfLine != -1 && indexOfColumn != -1 && indexOfLine < indexOfColumn){
                     String lineNumberStr = sb.substring(indexOfLine+5, indexOfColumn);
                     int lineNumberInt = Integer.parseInt(lineNumberStr);
                     if(lineNumberInt != -1){
                        res = file;
                        lineNumber = lineNumberInt;
                     }
                  }
               }
            }
         }
      }
      keyDelta.resetDelta();
      LastChangesFileWriter.resetLastChangesFiles(project);
      MarkerUtil.setProblemLoaderExceptionMarker(res, lineNumber, e.getMessage());
   }
   

   /**
    * Runs the {@link Proof}s available in the {@link IProject} dependent on the ProofManageMentProperties.
    * @param changedJavaFiles - {@link LinkedList} with all changed java{@link IFile}s
    * @param monitor - the {@link IProgressMonitor}
    * @throws Exception
    */
   public void runProofs(IProgressMonitor monitor) throws CoreException{
      proofElements = computeProofElementsAndUpdateProjectInfo();
      synchronized (keyDelta.lock) {
         changedJavaFiles = keyDelta.getChangedJavaFiles();
         keyDelta.resetDelta();
         selectProofElementsForBuild();
         LastChangesFileWriter.resetLastChangesFiles(project);
      }
      sortProofElements(editorSelection);
      cleanMarker();
      if(KeYProjectProperties.isAutoDeleteProofFiles(project)){
         cleanProofFolder(getAllFiles(), mainProofFolder);
      }
      //set up monitor
      monitor.beginTask("Building proofs for " + project.getName(), proofElements.size());
      initThreads(monitor);
      checkContractRecursion();
      monitor.done();
   }
   
   /**
    * Collects all {@link Proof}s available in the {@link IProject} and returns their
    * java{@link IFiles}, {@link SourceLocation}, {@link IMarker}, proof{@link IFolder} and {@link Contract} as 
    * {@link ProofElement}s in a {@link LinkedList}.
    * @return - the {@link LinkedList} with all {@link ProofElement}s
    * @throws CoreException 
    */
   private LinkedList<ProofElement> computeProofElementsAndUpdateProjectInfo() throws CoreException {
      ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
      Set<KeYJavaType> kjts = environment.getJavaInfo().getAllKeYJavaTypes();
      KeYJavaType[] kjtsarr = KeYUtil.sortKeYJavaTypes(kjts);
      LinkedList<ProofElement> proofElements = new LinkedList<ProofElement>();
      Map<AbstractTypeContainer, Integer> typeIndexMap = new HashMap<AbstractTypeContainer, Integer>();
      int packageIndex = 0;
      Map<String, PackageInfo> alreadyTreatedPackages = new HashMap<String, PackageInfo>();
      Map<String, TypeInfo> typeInfoMap = new HashMap<String, TypeInfo>();
      for (KeYJavaType type : kjtsarr) {
         // Find java file
         ImmutableSet<IObserverFunction> targets = environment.getSpecificationRepository().getContractTargets(type);
         Type javaType = type.getJavaType();
         IFile javaFile = null;
         SourceLocation typeScl = null;
         if (javaType instanceof JavaSourceElement) {
            JavaSourceElement javaElement = (JavaSourceElement) javaType;
            javaFile = searchFile(javaElement.getPositionInfo());
            typeScl = KeYUtil.convertToSourceLocation(javaElement.getPositionInfo());
            typeScl = KeYUtil.updateToTypeNameLocation(javaFile, typeScl);
         }
         // Find parent
         AbstractTypeContainer parentTypeContainer = null;
         String parentName = KeYTypeUtil.getParentName(environment.getServices(), type);
         if (!KeYTypeUtil.isType(environment.getServices(), parentName)) {
            if (parentName == null) {
               parentName = PackageInfo.DEFAULT_NAME;
            }
            parentTypeContainer = alreadyTreatedPackages.get(parentName);
            if (parentTypeContainer == null) {
               PackageInfo packageInfo = projectInfo.getPackage(parentName);
               if (packageInfo == null) {
                  packageInfo = new PackageInfo(projectInfo, parentName, javaFile != null ? javaFile.getParent() : null);
                  projectInfo.addPackage(packageInfo, packageIndex);
               }
               else {
                  removePackagesIfRequired(projectInfo, packageIndex, projectInfo.indexOfPackage(packageInfo));
               }
               typeIndexMap.put(packageInfo, Integer.valueOf(0));
               parentTypeContainer = packageInfo;
               packageIndex++;
               alreadyTreatedPackages.put(parentName, packageInfo);
            }
         }
         else {
            parentTypeContainer = typeInfoMap.get(parentName);
         }
         // Update type and methods
         TypeInfo typeInfo = parentTypeContainer.getType(type.getName());
         Integer typeIndex = typeIndexMap.get(parentTypeContainer);
         typeIndexMap.put(parentTypeContainer, typeIndex + 1);
         if (typeInfo == null) {
            typeInfo = new TypeInfo(projectInfo, type.getName(), javaFile, parentTypeContainer);
            parentTypeContainer.addType(typeInfo, typeIndex.intValue());
         }
         else {
            removeTypesIfRequired(parentTypeContainer, typeIndex.intValue(), parentTypeContainer.indexOfType(typeInfo));
         }
         typeIndexMap.put(typeInfo, Integer.valueOf(0)); // Ensure that inner types will be updated or removed at all in the end
         typeInfoMap.put(type.getFullName(), typeInfo);
         ImmutableList<IProgramMethod> methods = environment.getJavaInfo().getAllProgramMethods(type);
         methods = methods.prepend(environment.getJavaInfo().getConstructors(type));
         Map<IObserverFunction, AbstractContractContainer> targetMap = new HashMap<IObserverFunction, AbstractContractContainer>();
         int methodIndex = 0;
         for (IProgramMethod method : methods) {
            if (!method.isImplicit()) {
               // Add methods providing a specification or declared in project (not API)
               if (!KeYTypeUtil.isLibraryClass(method.getContainerType()) || !environment.getSpecificationRepository().getContracts(type, method).isEmpty()) {
                  String displayName = ClassTree.getDisplayName(environment.getServices(), method);
                  MethodInfo methodInfo = typeInfo.getMethod(displayName);
                  if (methodInfo == null) {
                     String[] parameterTypes = new String[method.getParameters().size()];
                     for (int i = 0; i < parameterTypes.length; i++) {
                        parameterTypes[i] = method.getParameters().get(i).getTypeReference().getKeYJavaType().getFullName();
                     }
                     methodInfo = new MethodInfo(projectInfo, typeInfo, displayName, method.getName(), method.getContainerType().getFullName(), searchFile(method.getContainerType()), parameterTypes);
                     typeInfo.addMethod(methodInfo, methodIndex);
                  }
                  else {
                     methodInfo.setDeclaringType(method.getContainerType().getFullName());
                     methodInfo.setDeclaringFile(searchFile(method.getContainerType()));
                     removeMethodsIfRequired(typeInfo, methodIndex, typeInfo.indexOfMethod(methodInfo));
                  }
                  targetMap.put(method, methodInfo);
                  methodIndex++;
               }
            }
         }
         removeMethodsIfRequired(typeInfo, methodIndex, typeInfo.countMethods());
         // Update observer function and contracts
         int observerFunctionIndex = 0;
         for (IObserverFunction target : targets) {
            AbstractContractContainer targetInfo;
            if (target instanceof IProgramMethod) {
               IProgramMethod pm = (IProgramMethod) target;
               if (KeYTypeUtil.isImplicitConstructor(pm)) {
                  pm = KeYTypeUtil.findExplicitConstructor(environment.getServices(), pm);
               }
               targetInfo = targetMap.get(pm);
            }
            else {
               targetInfo = targetMap.get(target);
               if (targetInfo == null) {
                  String displayName = ClassTree.getDisplayName(environment.getServices(), target);
                  targetInfo = typeInfo.getObserverFunction(displayName);
                  if (targetInfo == null) {
                     targetInfo = new ObserverFunctionInfo(projectInfo, typeInfo, displayName, target.getContainerType().getFullName(), searchFile(target.getContainerType()));
                     typeInfo.addObserverFunction((ObserverFunctionInfo)targetInfo, observerFunctionIndex);
                  }
                  else {
                     ((ObserverFunctionInfo) targetInfo).setDeclaringType(target.getContainerType().getFullName());
                     ((ObserverFunctionInfo) targetInfo).setDeclaringFile(searchFile(target.getContainerType()));
                     removeObserverFunctionsIfRequired(typeInfo, observerFunctionIndex, typeInfo.indexOfObserverFunction((ObserverFunctionInfo)targetInfo));
                  }
                  targetMap.put(target, targetInfo);
                  observerFunctionIndex++;
               }
            }
            if (targetInfo != null) {
               SourceLocation targetLocation = typeScl;
               if (target instanceof IProgramMethod) {
                  IProgramMethod progMethod = (IProgramMethod) target;
                  if(progMethod.getContainerType().getJavaType().equals(javaType)){
                     targetLocation = KeYUtil.convertToSourceLocation(progMethod.getPositionInfo());
                     targetLocation = KeYUtil.updateToMethodNameLocation(javaFile, targetLocation);
                  }
               }
               ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getContracts(type, target);
               int contractIndex = 0;
               for (Contract contract : contracts) {
                  Assert.isTrue(target == contract.getTarget());
                  IFolder proofFolder = KeYResourcesUtil.getProofFolder(javaFile);
                  IFile proofFile = KeYResourcesUtil.getProofFile(contract.getName(), proofFolder.getFullPath());
                  IFile metaFile = KeYResourcesUtil.getProofMetaFile(proofFile);
                  IMarker proofMarker = MarkerUtil.getProofMarker(javaFile, targetLocation, proofFile);
                  List<IMarker> recursionMarker = MarkerUtil.getRecursionMarker(javaFile, targetLocation, proofFile);
                  proofElements.add(new ProofElement(javaFile, targetLocation, environment, proofFolder, proofFile, metaFile, proofMarker, recursionMarker, contract));
                  ContractInfo contractInfo = targetInfo.getContract(contract.getName());
                  if (contractInfo == null) {
                     ContractModality modalityInfo = null;
                     if (contract instanceof FunctionalOperationContract) {
                        Modality modality = ((FunctionalOperationContract) contract).getModality();
                        if (Modality.BOX == modality || Modality.BOX_TRANSACTION == modality) {
                           modalityInfo = ContractModality.BOX;
                        }
                        else if (Modality.DIA == modality || Modality.DIA_TRANSACTION == modality) {
                           modalityInfo = ContractModality.DIAMOND;
                        }
                     }
                     contractInfo = new ContractInfo(targetInfo, contract.getName(), modalityInfo, proofFile, metaFile);
                     targetInfo.addContract(contractInfo, contractIndex);
                  }
                  else {
                     removeContractsIfRequired(targetInfo, contractIndex, targetInfo.indexOfContract(contractInfo));
                  }
                  contractIndex++;
               }
               removeContractsIfRequired(targetInfo, contractIndex, targetInfo.countContracts());
            }
         }
         removeObserverFunctionsIfRequired(typeInfo, observerFunctionIndex, typeInfo.countObserverFunctions());
         typeIndex++;
      }
      for (Entry<AbstractTypeContainer, Integer> entry : typeIndexMap.entrySet()) {
         removeTypesIfRequired(entry.getKey(), entry.getValue().intValue(), entry.getKey().countTypes());
      }
      removePackagesIfRequired(projectInfo, packageIndex, projectInfo.countPackages());
      ProjectInfoManager.getInstance().save(projectInfo);
      return proofElements;
   }
   
   /**
    * Searches the file specified by the given {@link KeYJavaType}.
    * @param positionInfo The {@link KeYJavaType} to search file for.
    * @return The found {@link IFile} or {@code null} if not available.
    */   
   protected IFile searchFile(KeYJavaType containerType) {
      IFile result = null;
      if (containerType != null) {
         Type javaType = containerType.getJavaType();
         if (javaType instanceof JavaSourceElement) {
            result = searchFile(((JavaSourceElement) javaType).getPositionInfo());
         }
      }
      return result;
   }

   /**
    * Searches the file specified by the given {@link PositionInfo}.
    * @param positionInfo The {@link PositionInfo} to search file for.
    * @return The found {@link IFile} or {@code null} if not available.
    */
   protected IFile searchFile(PositionInfo positionInfo) {
      if (positionInfo != null && !PositionInfo.UNDEFINED.equals(positionInfo)) {
         String fileName = SymbolicExecutionUtil.getSourcePath(positionInfo);
         IPath location = new Path(fileName);
         IPath relatviePath = location.makeRelativeTo(project.getLocation().removeLastSegments(1));
         return ResourcesPlugin.getWorkspace().getRoot().getFile(relatviePath);
      }
      return null;
   }

   /**
    * Removes all {@link PackageInfo} between the given indices.
    * @param projectInfo The {@link ProjectInfo} to remove {@link PackageInfo}s in.
    * @param startIndex The start index.
    * @param endIndex The end index.
    */
   protected void removePackagesIfRequired(ProjectInfo projectInfo, int startIndex, int endIndex) {
      if (endIndex > startIndex) {
         List<PackageInfo> toRemove = new LinkedList<PackageInfo>();
         for (int i = startIndex; i < endIndex; i++) {
            toRemove.add(projectInfo.getPackage(i));
         }
         projectInfo.removePackages(toRemove);
      }
   }

   /**
    * Removes all {@link TypeInfo} between the given indices.
    * @param tcInfo The {@link AbstractTypeContainer} to remove {@link TypeInfo}s in.
    * @param startIndex The start index.
    * @param endIndex The end index.
    */
   protected void removeTypesIfRequired(AbstractTypeContainer tcInfo, int startIndex, int endIndex) {
      if (endIndex > startIndex) {
         List<TypeInfo> toRemove = new LinkedList<TypeInfo>();
         for (int i = startIndex; i < endIndex; i++) {
            toRemove.add(tcInfo.getType(i));
         }
         tcInfo.removeTypes(toRemove);
      }
   }
   
   /**
    * Removes all {@link MethodInfo} between the given indices.
    * @param typeInfo The {@link TypeInfo} to remove {@link MethodInfo}s in.
    * @param startIndex The start index.
    * @param endIndex The end index.
    */
   protected void removeMethodsIfRequired(TypeInfo typeInfo, int startIndex, int endIndex) {
      if (endIndex > startIndex) {
         List<MethodInfo> toRemove = new LinkedList<MethodInfo>();
         for (int i = startIndex; i < endIndex; i++) {
            toRemove.add(typeInfo.getMethod(i));
         }
         typeInfo.removeMethods(toRemove);
      }
   }
   
   /**
    * Removes all {@link ObserverFunctionInfo} between the given indices.
    * @param typeInfo The {@link TypeInfo} to remove {@link ObserverFunctionInfo}s in.
    * @param startIndex The start index.
    * @param endIndex The end index.
    */
   protected void removeObserverFunctionsIfRequired(TypeInfo typeInfo, int startIndex, int endIndex) {
      if (endIndex > startIndex) {
         List<ObserverFunctionInfo> toRemove = new LinkedList<ObserverFunctionInfo>();
         for (int i = startIndex; i < endIndex; i++) {
            toRemove.add(typeInfo.getObserverFunction(i));
         }
         typeInfo.removeObserverFunctions(toRemove);
      }
   }
   
   /**
    * Removes all {@link ContractInfo} between the given indices.
    * @param ccInfo The {@link AbstractContractContainer} to remove {@link ContractInfo}s in.
    * @param startIndex The start index.
    * @param endIndex The end index.
    */
   protected void removeContractsIfRequired(AbstractContractContainer ccInfo, int startIndex, int endIndex) {
      if (endIndex > startIndex) {
         List<ContractInfo> toRemove = new LinkedList<ContractInfo>();
         for (int i = startIndex; i < endIndex; i++) {
            toRemove.add(ccInfo.getContract(i));
         }
         ccInfo.removeContracts(toRemove);
      }
   }
   
   
   /**
    * Checks for every {@link ProofElement} if it is outdated.
    * @return a {@link List<ProofElement>} that contains the updated {@link ProofElements}.
    */
   private void selectProofElementsForBuild() {
      for(ProofElement pe : proofElements){
         boolean build = false;
         if(buildType == KeYProjectBuildJob.FULL_BUILD 
               || (buildType == KeYProjectBuildJob.AUTO_BUILD && !KeYProjectProperties.isEnableBuildRequiredProofsOnly(project))){
            build = true;
         }
         else if(buildType == KeYProjectBuildJob.STARTUP_BUILD || buildType == KeYProjectBuildJob.MANUAL_BUILD){
            build = pe.getOutdated();
         }
         else if(buildType == KeYProjectBuildJob.AUTO_BUILD){
            if(pe.getOutdated()){
               build = true;
            }
            else{
               try{
                  LinkedList<IType> javaTypes = collectAllJavaITypes();
                  if(MD5changed(pe) || typeOrSubTypeChanged(pe.getTypeElements(), javaTypes) || superTypeChanged(pe, javaTypes)){
                     build = true;
                  }
               }
               catch (JavaModelException e){
                  build = true;
                  LogUtil.getLogger().logError(e);
               }
            }
         }
         if(build){
            pe.setBuild(true);
            if(!pe.getOutdated()){
               pe.setOutdated(true);
               MarkerUtil.setOutdated(pe, true);
               if(pe.hasMetaFile() && pe.hasProofFile()){
                  try {
                     keyDelta.addJobChangedFile(pe.getMetaFile());
                     ProofMetaFileWriter.writeMetaFile(pe);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
      }
   }
   
   
   /**
    * Sorts all {@link ProofElement}s in the following order: Selected method, active editor proofs, open editor proofs, affected/outdated proofs, other proofs.
    * @param editorSelection - the current workbench state of the editor windows.
    */
   private void sortProofElements(EditorSelection editorSelection) {
      if(editorSelection != null){
         List<ProofElement> sortedProofs = new LinkedList<ProofElement>();
         //Active selection
         List<ProofElement> activeMethodProofs = new LinkedList<ProofElement>();
         IMethod selectedMethod = editorSelection.getSelectedMethod();
         IFile activeFile = editorSelection.getActiveFile();
         if(selectedMethod != null && activeFile != null && activeFile.exists() && activeFile.equals(selectedMethod.getResource())){
            activeMethodProofs = KeYResourcesUtil.getProofElementsForMethod(proofElements, selectedMethod);
         }
         sortedProofs.addAll(activeMethodProofs);
         //Proofs of active file
         List<ProofElement> activeFileProofs = getProofsForFile(activeFile);
         for(ProofElement pe : activeFileProofs){
            if(!activeMethodProofs.contains(pe)){
               sortedProofs.add(pe);
            }
         }
         //Open file proofs
         List<IFile> openFiles = editorSelection.getOpenFiles();
         List<ProofElement> openFilesProofs = new LinkedList<ProofElement>();
         for(IFile openFile : openFiles){
            openFilesProofs.addAll(getProofsForFile(openFile));
         }
         sortedProofs.addAll(openFilesProofs);
         //Outdated proofs
         List<ProofElement> outdatedProofs = new LinkedList<ProofElement>();
         for(ProofElement pe : proofElements){
            if(pe.getBuild() && !activeFileProofs.contains(pe) && !openFilesProofs.contains(pe)){
               outdatedProofs.add(pe);
            }
         }
         sortedProofs.addAll(outdatedProofs);
         //Other proofs
         List<ProofElement> otherProofs = new LinkedList<ProofElement>();
         for(ProofElement pe : proofElements){
            if(!activeFileProofs.contains(pe) && !openFilesProofs.contains(pe) && !outdatedProofs.contains(pe)){
               otherProofs.add(pe);
            }
         }
         sortedProofs.addAll(otherProofs);
         if(proofElements.size() == sortedProofs.size()){
            proofElements = sortedProofs;  
         }
         else{
            System.out.println("Not all or more proofs then available are sorted!");
         }
      }    
   }
   
   
   /**
    * Collects all {@link ProofElement}s associated with the given {@link IFile}.
    * @param file - the {@link IFile} to use
    * @return a {@link List<ProofElement>} with all associated {@link ProofElement}s
    */
   private List<ProofElement> getProofsForFile(IFile file){         
      List<ProofElement> fileProofs = new LinkedList<ProofElement>();
      IJavaElement javaElement = JavaCore.create(file);
      if(file != null && javaElement != null){
         for(ProofElement pe : proofElements){
            if(pe != null && file.equals(pe.getJavaFile())){
               fileProofs.add(pe);
            }
         }
      }
      else if (file != null && 
               (KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(file.getFileExtension()) || 
                KeYResourcesUtil.META_FILE_EXTENSION.equals(file.getFileExtension()))) {
         for(ProofElement pe : proofElements){
            if(pe != null && file.equals(pe.getProofFile())){
               fileProofs.add(pe);
               break;
            }
            else if(pe != null && file.equals(pe.getMetaFile())){
               fileProofs.add(pe);
               break;
            }
         }
      }
      return fileProofs;
   }
   
   
   private void cleanMarker() {
      List<IMarker> peMarker = new LinkedList<IMarker>();
      for(ProofElement pe : proofElements){
         IMarker proofMarker = pe.getProofMarker();
         if(proofMarker != null && proofMarker.exists()){
            peMarker.add(proofMarker);
         }
         List<IMarker> recursionMarker = pe.getRecursionMarker();
         for(IMarker marker : recursionMarker){
            if(marker != null && marker.exists()){
               peMarker.add(marker);
            }
         }
      }
      LinkedList<IMarker> allMarker = MarkerUtil.getAllKeYMarker(project, IResource.DEPTH_INFINITE);
      for(IMarker marker : allMarker){
         if(!peMarker.contains(marker)){
            try{
               marker.delete();
            }
            catch (CoreException e){
               LogUtil.getLogger().logError(e);
            }
         }
      }
   }
   
   
   /**
    * Cleans every {@link IFolder} in the given {@link IFolder} by removing all files which are not 
    * listed in the given {@link LinkedList}. Empty {@link IFolder} will be deleted too.
    * @param proofFiles - the {@link LinkedList} to use
    * @param folder - the {@link IFolder} to start at
    * @throws CoreException Occurred Exception
    */
   private void cleanProofFolder(LinkedList<IFile> proofFiles, IFolder folder) throws CoreException {
      if(folder.exists()){
         IResource[] members = folder.members();
         for(IResource res : members){
            if(res.getType() == IResource.FILE){
               if(!proofFiles.contains(res) && 
                  !ProjectInfoManager.getInstance().isProjectInfoFile((IFile)res) &&
                  !LogManager.getInstance().isLogFile((IFile)res) && !KeYResourcesUtil.isLastChangesFile((IFile) res)) {
                  keyDelta.addJobChangedFile((IFile) res);
                  res.delete(true, null);
               }
            }
            else if(res.getType() == IResource.FOLDER){
               cleanProofFolder(proofFiles, (IFolder) res);
            }
         }
         if(folder.members().length == 0){
            folder.delete(true, null);
         }
      }
   }
   
   
   /**
    * Initializes the {@link Thread}s and creates the {@link ProofRunnable}s. While 
    * the {@link Thread}s are alive completed {@link Proof}s are saved periodically. 
    * @param proofElements
    * @param changedJavaFiles
    * @param monitor
    * @throws Exception 
    */
   private void initThreads(IProgressMonitor monitor) {
      proofQueue = Collections.synchronizedList(KeYResourcesUtil.cloneList(proofElements));

      int numOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      int numOfProofs = getNumOfProofsToDo();
      if(numOfProofs < numOfThreads){
         numOfThreads = numOfProofs;
      }
      Thread[] threads = null;
      if (KeYProjectProperties.isEnableMultiThreading(project)) {
         threads = new Thread[numOfThreads];
         for (int i = 0; i < threads.length; i++) {

            ProofRunnable run = new ProofRunnable(project, KeYResourcesUtil.cloneList(proofElements), proofQueue, cloneEnvironment(), monitor);
            threads[i] = new Thread(run);
         }
         for(Thread thread : threads){
            thread.start();
         }
      }
      else{
         threads = new Thread[1];
         ProofRunnable run = new ProofRunnable(project, proofElements,proofQueue, environment, monitor);
         Thread thread = new Thread(run);
         threads[0] = thread;
         thread.start();
      } 
      boolean threadsAlive = true;
      while(threadsAlive){
         threadsAlive = threadsAlive(threads);
         saveProofs();
         ObjectUtil.sleep(10);
      }
   }
   
   
   private void saveProofs() {
      Pair<ProofElement, InputStream> proofToSave = null;
      while((proofToSave = getProofToSave()) != null){
         try{
            ProofElement pe = proofToSave.first;
            InputStream is = proofToSave.second;
            KeYProjectDelta keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
            keyDelta.addJobChangedFile(pe.getProofFile());
            saveProof(pe.getProofFile(), is, pe.getProofClosed());
            keyDelta.addJobChangedFile(pe.getMetaFile());
            ProofMetaFileWriter.writeMetaFile(pe);
            MarkerUtil.setMarker(pe);
         }
         catch (Exception e){
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   private void saveProof(IFile proofFile, InputStream is, boolean isClosed) throws CoreException{
      IFolder proofFolder = KeYResourcesUtil.createFolder(proofFile);
      if(proofFolder != null && proofFolder.exists()){
         if (proofFile.exists()) {
            proofFile.setContents(is, true, true, null);
         }
         else {
            proofFile.create(is, true, null);
         }
         KeYResourcesUtil.setProofClosed(proofFile, Boolean.valueOf(isClosed));
      }
   }
   
   public synchronized Pair<ProofElement, InputStream> getProofToSave(){
      synchronized (proofsToSave) {
         if(!proofsToSave.isEmpty()){
            return proofsToSave.remove(0);
         }
         return null;
      }
   }
   
   
   private int getNumOfProofsToDo(){
      int num = 0;
      for(ProofElement pe : proofElements){
         if(pe.getBuild()){
            num++;
         }
      }
      return num;
   }
   
   
   /**
    * Returns if the given {@link Thread}s are alive.
    * @param threads - the {@link Thread}s to check
    * @return true if at least one {@link Thread} is alive. false otherwise
    */
   private boolean threadsAlive(Thread[] threads){
      for(Thread thread : threads){
         if (thread.isAlive()){
            return true;
         }
      }
      return false;
   }
   
   
   /**
    * Clones the global {@link KeYEnvironment}.
    * @return the cloned {@link KeYEnvironment}
    */
   private KeYEnvironment<CustomUserInterface> cloneEnvironment() {
      InitConfig sourceInitConfig = environment.getInitConfig();
      // Create new profile which has separate OneStepSimplifier instance
      JavaProfile profile = new JavaProfile();
      // Create new InitConfig and initialize it with value from initial one.
      InitConfig initConfig = new InitConfig(environment.getServices().copy(profile, false));
      initConfig.setActivatedChoices(sourceInitConfig.getActivatedChoices());
      ProofSettings clonedSettings = sourceInitConfig.getSettings() != null ? new ProofSettings(sourceInitConfig.getSettings()) : null;
      initConfig.setSettings(clonedSettings);
      initConfig.setTaclet2Builder(sourceInitConfig.getTaclet2Builder());
      initConfig.setTaclets(sourceInitConfig.getTaclets());
      // Create new ProofEnvironment and initialize it with values from initial one.
      initConfig.getServices().setJavaModel(sourceInitConfig.getServices().getJavaModel());
      KeYEnvironment<CustomUserInterface> keyEnv = new KeYEnvironment<CustomUserInterface>(new CustomUserInterface(false), initConfig);
      return keyEnv;
   }
   

   /**
    * Checks all given {@link ProofElement}s for cycling contract recursion
    * @param proofElements - the {@link ProofElement} to check
    * @throws CoreException
    */
   private void checkContractRecursion() throws CoreException {
      HashSet<List<ProofElement>> cycles = new LinkedHashSet<List<ProofElement>>();
      findCycles(cycles);
      removeAllRecursionMarker();
      for(List<ProofElement> cycle : cycles){
         MarkerUtil.setRecursionMarker(cycle);
      }
      restoreOldMarkerForRemovedCycles();
      setInRecursionCycleProofFileProperty(cycles);
   }

   /**
    * Updates the {@link IResource} persistent property
    * KeYResourcesUtil#isProofInRecursionCycle(IFile)
    * of all proof files in the proof folder.
    * @throws CoreException
    */
   private void setInRecursionCycleProofFileProperty(HashSet<List<ProofElement>> cycles) throws CoreException {
      // Compute all proof files which are part of at least one cycle
      final Map<IFile, List<IFile>> cycleMap = new HashMap<IFile, List<IFile>>();
      for (List<ProofElement> cycle : cycles) {
         List<IFile> cycleFiles = new LinkedList<IFile>();
         for (ProofElement pe : cycle) {
            cycleFiles.add(pe.getProofFile());
            cycleMap.put(pe.getProofFile(), cycleFiles);
         }
      }
      // Update resource persistent property.
      mainProofFolder.accept(new IResourceVisitor() {
         @Override
         public boolean visit(IResource resource) throws CoreException {
            if (resource instanceof IFile) {
               IFile file = (IFile) resource;
               List<IFile> cycles = cycleMap.get(file);
               if (cycles != null) {
                  KeYResourcesUtil.setProofRecursionCycle(file, cycles);
               }
               else {
                  KeYResourcesUtil.setProofRecursionCycle(file, null);
               }
            }
            return true;
         }
      });
   }
   
   
   /**
    * Collects all proof- and meta{@link IFile}s from the given {@link LinkedList} of {@link ProofElement}s.
    * @param proofElements - the {@link ProofElement}s to use
    * @return a {@link LinkedList} with all proof- and meta{@link IFile}s
    */
   private LinkedList<IFile> getAllFiles(){
      LinkedList<IFile> proofFiles = new LinkedList<IFile>();
      for(ProofElement pe : proofElements){
         proofFiles.add(pe.getProofFile());
         proofFiles.add(pe.getMetaFile());
      }
      return proofFiles;
   }
   
   
   /**
    * Collects all {@link IType}s of the project.
    * @return a {@link LinkedList} with all {@link IType}s
    * @throws JavaModelException
    */
   private LinkedList<IType> collectAllJavaITypes() throws JavaModelException{
      LinkedList<IType> typeList = new LinkedList<IType>();
      IJavaProject javaProject = JavaCore.create(project);
      IPackageFragment[] packageFragments = javaProject.getPackageFragments();
      for(IPackageFragment packageFragment : packageFragments){
         ICompilationUnit[] units = packageFragment.getCompilationUnits();
         for(ICompilationUnit unit : units){
            IType[] types = unit.getTypes();
            for(IType type : types){
               typeList.add(type);
               typeList.addAll(collectAllJavaITypesForIType(type));
            }
         }
      }
      return typeList;
   }

   
   /**
    * Collects all {@link IType}s of the given {@link IType}.
    * @param type - the {@link IType} to use
    * @return all {@link IType}s of the given {@link IType}
    * @throws JavaModelException
    */
   private LinkedList<IType> collectAllJavaITypesForIType(IType type) throws JavaModelException{
      LinkedList<IType> types = new LinkedList<IType>();
      IType[] subTypes = type.getTypes();
      for(IType subType : subTypes){
         types.add(subType);
         types.addAll(collectAllJavaITypesForIType(subType));
      }
      return types;
   }
   
   
   /**
    * Checks if the MD5 of the proof{@link IFile} is different to the MD5 stored in the metafile.
    * @param proofFile - the proof{@link IFile} to use
    * @param pmfr - the {@link ProofMetaFileReader} to use
    * @return false if both MD5s are equal. true otherwise
    * @throws CoreException 
    * @throws IOException 
    */
   private static boolean MD5changed(ProofElement pe) {
      if(pe.getMD5() != null){
         if(pe.getProofFile().exists()){
            String proofFileHasCode;
            try {
               proofFileHasCode = ResourceUtil.computeContentMD5(pe.getProofFile());
            }
            catch (Exception e) {
               return true;
            }
            if(pe.getMD5().equals(proofFileHasCode)){
               return false;
            }
         }
      }
      return true;
   }
   

   /**
    * Checks if a type or a subtype from the metafile were changed.  
    * @param pmfr - the {@link ProofMetaFileReader} to use
    * @param javaTypes the {@link LinkedList} with all changed java{@link IFile}s
    * @return true if a type or a subtype was changed. false otherwise
    * @throws JavaModelException
    */
   private boolean typeOrSubTypeChanged(List<ProofMetaFileTypeElement> types, LinkedList<IType> javaTypes) {
      for(ProofMetaFileTypeElement type : types){
         List<String> subTypes = type.getSubTypes();
         if(typeChanged(type.getType(), javaTypes)){
            return true;
         }
         else if(subTypeChanged(type.getType(), subTypes, javaTypes)){
            return true;
         }
      }
      return false;
   }
   
   
   /**
    * Checks if the given type was changed.
    * @param type - the type to check
    * @param javaTypes - all {@link IType}s of the project
    * @return true if the type was changed. false otherwise
    * @throws JavaModelException
    */
   private boolean typeChanged(String type, List<IType> javaTypes) {
      IFile javaFile = getJavaFileForType(type, javaTypes);
      //check if type has changed itself
      if(changedJavaFiles.contains(javaFile)){
         return true;
      }
      return false;
   }
   
   
   /**
    * Checks if any subTypes of the given {@link ProofMetaFileTypeElement} were changed.
    * @param te - the {@link ProofMetaFileTypeElement} to use
    * @param javaTypes - all {@link IType}s of the project
    * @return true if any subTypes were changed. false otherwise
    * @throws JavaModelException
    */
   private boolean subTypeChanged(String type, List<String> subTypes, List<IType> javaTypes) {
      KeYJavaType kjt = getkeYJavaType(environment, type);
      ImmutableList<KeYJavaType> envSubKjts = environment.getJavaInfo().getAllSubtypes(kjt);      
      if(envSubKjts.size() != subTypes.size()){
         return true;
      }
      for(String subType : subTypes){
         if(typeChanged(subType, javaTypes)){
            return true;
         }
      }
      return false;
   }
   
   
   /**
    * Checks if any superTypes of the given {@link KeYJavaType} were changed.
    * @param kjt - the {@link KeYJavaType} to use
    * @param changedJavaFiles - all changed java{@link IFile}s
    * @param javaTypes - all {@link IType}s of the project
    * @return true if any superTypes were changed. false otherwise
    * @throws JavaModelException
    */
   private boolean superTypeChanged(ProofElement pe, LinkedList<IType> javaTypes) {
      KeYJavaType kjt = pe.getContract().getKJT();
      KeYJavaType envKjt = getkeYJavaType(environment, kjt.getFullName());
      if(envKjt != null){
         ImmutableList<KeYJavaType> envSuperKjts = environment.getJavaInfo().getAllSupertypes(envKjt);
         for(KeYJavaType envSuperKjt : envSuperKjts){
            IFile javaFile = getJavaFileForType(envSuperKjt.getFullName(), javaTypes);
            if(changedJavaFiles.contains(javaFile)){
               return true;
            }
         }
         return false;
      }
      return true;
   }

   
   /**
    * Returns the java{@link IFile} for the given metaType.
    * @param metaType - the given type
    * @param typeList - all {@link IType}s of the project
    * @return the java{@link IFile} for the given type
    * @throws JavaModelException
    */
   private IFile getJavaFileForType(String metaType, List<IType> typeList) {
      for(IType iType : typeList){
         String typeName = iType.getFullyQualifiedName('.');
         if(typeName.equalsIgnoreCase(metaType)){
            IPath filePath = iType.getResource().getFullPath();
            IFile javaFile = ResourcesPlugin.getWorkspace().getRoot().getFile(filePath);
            return javaFile;
         }
      }
      
      return null;
   }
   
   
   /**
    * Returns the {@link KeYJavaType} for the given fullName.
    * @param type - the types full name
    * @return the {@link KeYJavaType}
    */
   private KeYJavaType getkeYJavaType(KeYEnvironment<CustomUserInterface> env, String type){
      Set<KeYJavaType> envKjts = env.getServices().getJavaInfo().getAllKeYJavaTypes();
      for(KeYJavaType kjt : envKjts){
         if(type.equals(kjt.getFullName())){
            return kjt;
         }
      }
      return null;
   }
   
   
   private void restoreOldMarkerForRemovedCycles() {
      for(ProofElement pe : proofElements){
         if(pe.getProofMarker() == null && (pe.getRecursionMarker() == null || pe.getRecursionMarker().isEmpty())){
            if(pe.getMetaFile() != null && pe.getMetaFile().exists()){
               MarkerUtil.setMarker(pe);
            }
         }
      }
   }


   private void findCycles(HashSet<List<ProofElement>> cycles){
      Map<ProofElement, List<ProofElement>> usedContracts = new LinkedHashMap<ProofElement, List<ProofElement>>();
      for(ProofElement pe : proofElements){
         usedContracts.put(pe, KeYResourcesUtil.getProofElementsByProofFiles(pe.getUsedContracts(), proofElements));
      }
      for(ProofElement pe : proofElements){
         LinkedList<ProofElement> cycle = new LinkedList<ProofElement>();
         cycle.add(pe);
         searchCycle(cycle, cycles, usedContracts);
      }
   }
   
   private void searchCycle(List<ProofElement> cycle, HashSet<List<ProofElement>> cycles, Map<ProofElement, List<ProofElement>> usedContracts){
      List<ProofElement> succs = usedContracts.get(cycle.get(cycle.size()-1));
      for(ProofElement pe : succs){
         if(pe.equals(cycle.get(0))){
            //cycle found
            cycles.add(cycle);
         }
         else if(cycle.contains(pe)){
            return;
         }
         else{
            List<ProofElement> tmpCycle = KeYResourcesUtil.cloneList(cycle);
            tmpCycle.add(pe);
            searchCycle(tmpCycle, cycles, usedContracts); 
         }
      }
   }
   
   
   private void removeAllRecursionMarker() throws CoreException {
      for(ProofElement pe : proofElements){
         pe.setRecursionMarker(new LinkedList<IMarker>());
      }
      MarkerUtil.deleteKeYMarkerByType(project, IResource.DEPTH_INFINITE, MarkerUtil.RECURSIONMARKER_ID);
   }
}
