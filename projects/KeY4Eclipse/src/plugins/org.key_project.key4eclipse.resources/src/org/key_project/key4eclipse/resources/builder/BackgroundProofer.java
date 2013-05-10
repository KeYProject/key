package org.key_project.key4eclipse.resources.builder;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IMethod;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class BackgroundProofer {
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   
   public BackgroundProofer(IProject project) throws CoreException, ProblemLoaderException{
      final File location = ResourceUtil.getLocation(project);
      final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
      final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
      environment = KeYEnvironment.load(location, classPaths, bootClassPath);
   }
   
   /**
    * Collects all {@link FunctionalOperationContract}s of the given {@link IMethod}.
    * @param method - the given {@link Method}.
    * @param environment - the {@link KeYEnvironment} for this {@link IMethod}.
    * @return - An {@link ImmutableSet<FunctionOperationContract>} that holds all {@link FunctionalOperationContract}s found for the given {@link IMethod}.
    * @throws ProofInputException
    */
   public ImmutableSet<FunctionalOperationContract> collectAllContractsForMethod(IMethod method) throws ProofInputException {
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
   
   
   public Proof createProof(ProofOblInput obl, IFile file) throws ProofInputException, ProblemLoaderException, CoreException, IOException{
      //if proof does not exist, create it. else load it and run the automode.
      
      Proof proof;
      if(!file.exists()){
         proof = environment.createProof(obl);
         environment.getUi().startAndWaitForAutoMode(proof);   
      }
      else{
         File proofFile = file.getLocation().toFile();
         environment = KeYEnvironment.load(proofFile, null, null);
         proof = environment.getLoadedProof();
         if(!proof.closed()){
            environment.getUi().startAndWaitForAutoMode(proof);
         }
      }
      return proof;  
   }
   
   
   public void saveProof(Proof proof, IPath path) throws CoreException, IOException{
      IFile file = getProofIFile(proof.name().toString(), path);
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
   
   /**
    * Creates the {@link IFile} for the {@link Proof} that will be stored.
    * @param name - the name for the {@link IFile}.
    * @param path - the path for the {@link IFile}.
    * @return - the {@link IFile}.
    */
   public IFile getProofIFile(String name, IPath path){
      if(path != null && name != null){
         name = makePathValid(name);
         name = name + ".proof";
         path = path.append(name);
         IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
         return file;
      }
      else return null;
   }
   
   /**
    * Replaces invalid characters in the given {@link String} with '_' and returns a vaild {@link String}.
    * @param str - the {@link String} to be made valid.
    * @return the valid {@link String}
    */
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

   
   public LinkedList<ProofOblInput> createAllProofOblsForMethod(IMethod method) throws ProofInputException{
      LinkedList<ProofOblInput> proofObls = new LinkedList<ProofOblInput>();
      ImmutableSet<FunctionalOperationContract>  contracts = collectAllContractsForMethod(method);
      Iterator<FunctionalOperationContract> it = contracts.iterator();
      while (it.hasNext()) {
         FunctionalOperationContract contract = it.next();
         ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
         proofObls.add(input);
      }
      return proofObls;
   }
   

   
}
