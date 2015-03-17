package org.key_project.key4eclipse.resources.io;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Compares {@link ProofMetaReferences} with the current code state
 * @author Stefan Käsdorf
 */
public class ProofMetaReferencesComparator {

   private ProofElement pe;
   private ProofMetaReferences references;
   private KeYEnvironment<?> env;
   private Set<IFile> changedJavaFiles;
   
   public ProofMetaReferencesComparator(ProofElement pe, KeYEnvironment<?> env, Set<IFile> changedJavaFiles) {
      this.pe = pe;
      this.references = pe.getProofMetaReferences();
      this.env = env;
      this.changedJavaFiles = changedJavaFiles;
   }

   public boolean compareReferences() {
      if(references != null){
         if (!(contractChanged() || axiomChanged() || invariantChanged() || accessesChanged() || callMethodsChanged() || inlineMethodsChanged() || contractsChanged())) {
            return false;
         }
      }
      return true;
   }
   
   private boolean hasKjtChanged(KeYJavaType kjt){
      IFile javaFile = getKjtJavaFile(kjt);
      if(javaFile != null && !changedJavaFiles.contains(javaFile)){
         return false;
      }
      return true;
   }
   
   private IFile getKjtJavaFile(KeYJavaType kjt){
      IFile file = null;
      if(kjt != null && kjt.getJavaType() instanceof TypeDeclaration){
         TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
         String pos = typeDecl.getPositionInfo().getFileName();
         IPath path = new Path(pos);
         file = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(path);
      }
      return file;
   }


   private boolean contractChanged() {
      if (KeYResourcesUtil.contractToString(pe.getContract()).equals(references.getContract())) {
         return false;
      }
      return true;
   }


   private boolean axiomChanged() {
      List<ProofMetaReferenceAxiom> axioms = references.getAxioms();
      for(ProofMetaReferenceAxiom axiom : axioms){
         if(axiom != null){
            KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(axiom.getKjt());
            if(kjt != null){
               if(hasKjtChanged(kjt)){
                  ImmutableSet<ClassAxiom> classAxioms = env.getSpecificationRepository().getClassAxioms(kjt);
                  for(ClassAxiom classAxiom : classAxioms) {
                     if(classAxiom instanceof RepresentsAxiom && classAxiom.getName().equals(axiom.getName())) {
                        RepresentsAxiom repAxiom = (RepresentsAxiom) classAxiom;
                        if(!axiom.getOriginalRep().equals(KeYResourcesUtil.repAxiomToString(repAxiom))){
                           return true;
                        }
                     }
                  }
               }
            }
            else {
               return true;
            }
         }
      }
      return false;
   }


   private boolean invariantChanged() {
      List<ProofMetaReferenceInvariant> invariants = references.getInvariants();
      for(ProofMetaReferenceInvariant invariant : invariants){
         if (invariant != null) {
            KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(invariant.getKjt());
            if (kjt != null) {
               if(hasKjtChanged(kjt)){
                  ImmutableSet<ClassInvariant> classInvariants = env.getSpecificationRepository().getClassInvariants(kjt);
                  for(ClassInvariant classInvariant : classInvariants) {
                     if(classInvariant.getName().equals(invariant.getName()) && !invariant.getOriginalInv().equals(KeYResourcesUtil.invariantToString(classInvariant))) {
                        return true;
                     }
                  }
               }
            }
            else {
               return true;
            }
         }
      }
      return false;
   }


   private boolean accessesChanged() {
      for (ProofMetaReferenceAccess access : references.getAccesses()) {
         if(accessChanged(access)){
            return true;
         }
      }
      return false;
   }


   private boolean accessChanged(ProofMetaReferenceAccess access) {
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(access.getKjt());
      if (kjt != null) {
         if(hasKjtChanged(kjt)){
            FieldDeclaration fieldDecl = KeYResourcesUtil.getFieldDeclFromKjt(kjt, access.getName());
            if(fieldDecl != null) {
               String type = fieldDecl.getTypeReference().toString();
               VisibilityModifier vm = fieldDecl.getVisibilityModifier();
               String visibility = vm == null ? "" : vm.toString();
               boolean isStatic = fieldDecl.isStatic();
               boolean isFinal = fieldDecl.isFinal();
               if(type.equals(access.getType()) && visibility.equals(access.getVisibility()) 
                     && isStatic == access.isStatic() && isFinal == access.isFinal()) {
                  if(isFinal) {
                     String initializer = fieldDecl.getFieldSpecifications().get(0).getInitializer().toString();
                     return !initializer.equals(access.getInitializer());
                  }
                  return false;
               }
            }
         }
         else {
            return false;
         }
      }
      return true;
   }


   private boolean callMethodsChanged() {
      for (ProofMetaReferenceCallMethod callMethod : references.getCallMethods()) {
         if (callMethodChanged(callMethod)) {
            return true;
         }
      }
      return false;
   }


   private boolean callMethodChanged(ProofMetaReferenceCallMethod callMethod) {
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(callMethod.getKjt());
      if(kjt != null){
         Map<KeYJavaType, IProgramMethod> implementations = KeYResourcesUtil.getKjtsOfAllImplementations(env, kjt, callMethod.getName(), callMethod.getParameters());
         String implementationsString = KeYResourcesUtil.implementationTypesToString(implementations);
         if(implementationsString.equals(callMethod.getImplementations())) {
            return false;
         }
      }
      return true;
   }


   private boolean inlineMethodsChanged() {
      for (ProofMetaReferenceMethod inlineMethod : references.getInlineMethods()) {
         if (inlineMethodChanged(inlineMethod)) {
            return true;
         }
      }
      return false;
   }
   
   
   private boolean inlineMethodChanged(ProofMetaReferenceMethod method) {
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(method.getKjt());
      if(kjt != null){
         if(hasKjtChanged(kjt)){
            IProgramMethod pm = KeYResourcesUtil.getMethodForKjt(kjt, method.getName(), method.getParameters());
            if(pm != null){
               String src = KeYResourcesUtil.createSourceString(pm.getMethodDeclaration());
               if (method.getSource().equals(src)) {
                  return false;
               }
            }
         }
         else {
            return false;
         }
      }
      return true;
   }


   private boolean contractsChanged() {
      for (ProofMetaReferenceContract contract : references.getContracts()) {
         Contract c = env.getSpecificationRepository().getContractByName(contract.getName());
         if (c == null || !contract.getContract().equals(c.toString())) {
            return true;
         }
      }
      return false;
   }

}
