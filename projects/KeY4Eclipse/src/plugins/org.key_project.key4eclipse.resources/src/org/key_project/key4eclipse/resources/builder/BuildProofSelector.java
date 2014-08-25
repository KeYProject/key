package org.key_project.key4eclipse.resources.builder;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.resources.io.ProofMetaFileReader;
import org.key_project.key4eclipse.resources.io.ProofMetaFileTypeElement;
import org.key_project.key4eclipse.resources.marker.MarkerManager;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Class for checking the actuality of proofs.
 * @author Stefan Käsdorf
 */
public class BuildProofSelector {
   
   private IProject project;
   private List<ProofElement> proofElements;
   private List<IFile> changedJavaFiles;
   private KeYEnvironment<CustomUserInterface> environment;
   private KeYProjectBuildInstruction inst;
   
   public BuildProofSelector(IProject project, List<ProofElement> proofElements, List<IFile> changedJavaFiles, KeYEnvironment<CustomUserInterface> environment, KeYProjectBuildInstruction inst){
      this.project = project;
      this.proofElements = proofElements;
      this.changedJavaFiles = changedJavaFiles;
      this.environment = environment;
      this.inst = inst;
   }
   
   
   /**
    * Checks for every {@link ProofElement} if it is outdated.
    * @return a {@link List<ProofElement>} that contains the updated {@link ProofElements}.
    */
   public void updateProofElements() {
      List<ProofElement> proofElementsToCheck = getProofsToCheck();
      MarkerManager markerManager = new MarkerManager();
      for(ProofElement pe : proofElementsToCheck){
         boolean build = false;
         try{
            if((!KeYProjectProperties.isEnableBuildRequiredProofsOnly(project)) || inst.getClean() || inst.getElementsToBuild() != null){
               build = true;
            }
            else{
               IFile metaFile = pe.getMetaFile();
               if(pe.getOutdated()){
                  build = true;
               }
               else if((pe.getProofMarker() == null || !pe.getProofMarker().exists()) 
                  && (pe.getRecursionMarker() == null || pe.getRecursionMarker().isEmpty())){
                  build = true;
               }
               else if(metaFile.exists()){
                  ProofMetaFileReader pmfr = new ProofMetaFileReader(metaFile);
                  LinkedList<IType> javaTypes = collectAllJavaITypes();
                  if(MD5changed(pe.getProofFile(), pmfr) || typeOrSubTypeChanged(pe, pmfr, javaTypes) || superTypeChanged(pe, javaTypes)){
                     build = true;
                  }
               }
               else{
                  build = true;
               }
            }
         }
         catch(Exception e){
            LogUtil.getLogger().logError(e);
            build = true;
         }
         
         if(build){
            markerManager.setOutdated(pe);
         }            
      }
      for(ProofElement pe : proofElements){
         if(pe.getProofFile() != null && pe.getProofFile().exists() 
               && pe.getMetaFile() != null && pe.getMetaFile().exists()){
            try{
               ProofMetaFileReader pmfr = new ProofMetaFileReader(pe.getMetaFile());
               pe.setProofClosed(pmfr.getProofClosed());
               pe.setMarkerMsg(pmfr.getMarkerMessage());
               pe.setUsedContracts(KeYResourcesUtil.getProofElementsByProofFiles(pmfr.getUsedContracts(), proofElements));
            }
            catch (Exception e){
               LogUtil.getLogger().logError(e);
            }
         }
      }
   }
   
   
   private List<ProofElement> getProofsToCheck(){
      if(inst.getClean() || inst.getElementsToBuild() == null){
         return proofElements;
      }
      else{
         List<ProofElement> elementsToCheck = new LinkedList<ProofElement>();
         List<Object> elementsToBuild = inst.getElementsToBuild();
         for(Object obj : elementsToBuild){
            if(obj instanceof IFile){
               IFile file = (IFile) obj;
               for(ProofElement pe : proofElements){
                  if(pe != null){
                     if(file.equals(pe.getJavaFile()) || file.equals(pe.getProofFile())){
                        elementsToCheck.add(pe);
                     }
                  }
               }
            }
            else if(obj instanceof IMethod){
               IMethod method = (IMethod) obj;
               elementsToCheck.addAll(KeYResourcesUtil.getProofElementsForMethod(proofElements, method));
            }
         }
         return elementsToCheck;
      }
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
   private static boolean MD5changed(IFile proofFile, ProofMetaFileReader pmfr) throws IOException, CoreException{
      if(proofFile.exists()){
         String metaFilesProofMD5 = pmfr.getProofFileMD5();
         String proofFileHasCode = ResourceUtil.computeContentMD5(proofFile);
         if(metaFilesProofMD5.equals(proofFileHasCode)){
            return false;
         }
         else{
            return true;
         }
      }
      else{
         return true;
      }
   }
   

   /**
    * Checks if a type or a subtype from the metafile were changed.  
    * @param pmfr - the {@link ProofMetaFileReader} to use
    * @param javaTypes the {@link LinkedList} with all changed java{@link IFile}s
    * @return true if a type or a subtype was changed. false otherwise
    * @throws JavaModelException
    */
   private boolean typeOrSubTypeChanged(ProofElement pe, ProofMetaFileReader pmfr, LinkedList<IType> javaTypes) throws JavaModelException{
      LinkedList<ProofMetaFileTypeElement> typeElements = pmfr.getTypeElements();
      for(ProofMetaFileTypeElement te : typeElements){
         if(typeChanged(te.getType(), javaTypes)){
            return true;
         }
         else if(subTypeChanged(pe, te, javaTypes)){
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
   private boolean typeChanged(String type, LinkedList<IType> javaTypes) throws JavaModelException{
      IFile javaFile = getJavaFileForType(type, javaTypes);
      //check if type has changed itself
      if(changedJavaFiles.contains(javaFile)){
         return true;
      }
      else {
         return false;
      }
   }
   
   
   /**
    * Checks if any subTypes of the given {@link ProofMetaFileTypeElement} were changed.
    * @param te - the {@link ProofMetaFileTypeElement} to use
    * @param javaTypes - all {@link IType}s of the project
    * @return true if any subTypes were changed. false otherwise
    * @throws JavaModelException
    */
   private boolean subTypeChanged(ProofElement pe, ProofMetaFileTypeElement te, LinkedList<IType> javaTypes) throws JavaModelException{
      String type = te.getType();
      KeYJavaType kjt = getkeYJavaType(environment, type);
      ImmutableList<KeYJavaType> envSubKjts = environment.getJavaInfo().getAllSubtypes(kjt);
      
      LinkedList<String> subTypes = te.getSubTypes();
      
      if(envSubKjts.size() != subTypes.size()){
         return true;
      }
      else {
         for(String subType : subTypes){
            if(typeChanged(subType, javaTypes)){
               return true;
            }
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
   private boolean superTypeChanged(ProofElement pe, LinkedList<IType> javaTypes) throws JavaModelException{
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
      else{
         return true;
      }
   }

   
   /**
    * Returns the java{@link IFile} for the given metaType.
    * @param metaType - the given type
    * @param typeList - all {@link IType}s of the project
    * @return the java{@link IFile} for the given type
    * @throws JavaModelException
    */
   private IFile getJavaFileForType(String metaType, LinkedList<IType> typeList) throws JavaModelException{
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
}
