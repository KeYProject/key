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
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.util.Pair;

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
         if(contractChanged() || callMethodsChanged() || overloadOccured()){
            return true;
         }
         for(Map.Entry<String, ProofMetaPerTypeReferences> entry : references.getPerTypeReferences().entrySet()){
            String kjt = entry.getKey();
            if(hasKjtChanged(kjt)){
               ProofMetaPerTypeReferences ptRefs = entry.getValue();
               if(axiomChanged(ptRefs) 
                     || invariantChanged(ptRefs) 
                     || accessesChanged(ptRefs) 
                     || inlineMethodsChanged(ptRefs) 
                     || contractsChanged(ptRefs)){
                  return true;
               }
            }
         }
         return false;
      }
      return true;
   }
   
   private boolean overloadOccured() {
      for(ProofMetaReferenceCallMethod callMethod : references.getCallMethods()) {
         if(hasKjtChanged(callMethod.getKjt())){
            KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(callMethod.getKjt());
            if(kjt.getJavaType() instanceof TypeDeclaration){
               TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
               for(MemberDeclaration memberDecl : typeDecl.getMembers()) {
                  if (memberDecl instanceof IProgramMethod) {
                     IProgramMethod pm = (IProgramMethod) memberDecl;
                     if (pm.getFullName().equals(callMethod.getName()) && isParameterOverloading(callMethod.getParameters(), pm)) {
                        return true;
                     }
                  }
               }
            }
         }
      }
      return false;
   }
   
   private boolean isParameterOverloading(String base, IProgramMethod overload){
      String[] baseParameters = base.split(";");
      String overLoadParametersStr = KeYResourcesUtil.parametersToString(overload.getParameters());
      if(base.equals(overLoadParametersStr) || baseParameters.length != overload.getParameterDeclarationCount()){
         return false;
      }
      for(int i = 0; i < baseParameters.length; i++) {
         KeYJavaType overloadKjt = overload.getParameterDeclarationAt(i).getTypeReference().getKeYJavaType();
         KeYJavaType baseKjt = env.getJavaInfo().getKeYJavaType(baseParameters[i]);
         if(!baseKjt.equals(overloadKjt) && !env.getJavaInfo().getAllSubtypes(baseKjt).contains(overloadKjt)){
            return false;
         }
      }
      return true;
   }

   private boolean hasKjtChanged(String kjtStr){
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(kjtStr);
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
      String peContract = KeYResourcesUtil.contractToString(pe.getContract());
      if (peContract.equals(references.getContract())) {
         return false;
      }
      return true;
   }


   private boolean axiomChanged(ProofMetaPerTypeReferences ptRefs) {
      List<ProofMetaReferenceAxiom> axioms = ptRefs.getAxioms();
      for(ProofMetaReferenceAxiom axiom : axioms){
         if(axiom != null){
            KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(axiom.getKjt());
            if(kjt != null){
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
            else {
               return true;
            }
         }
      }
      return false;
   }


   private boolean invariantChanged(ProofMetaPerTypeReferences ptRefs) {
      for(ProofMetaReferenceInvariant invariant : ptRefs.getInvariants()){
         if (invariant != null) {
            KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(invariant.getKjt());
            if (kjt != null) {
               ImmutableSet<ClassInvariant> classInvariants = env.getSpecificationRepository().getClassInvariants(kjt);
               for(ClassInvariant classInvariant : classInvariants) {
                  if(classInvariant.getName().equals(invariant.getName()) && !invariant.getOriginalInv().equals(KeYResourcesUtil.invariantToString(classInvariant))) {
                     return true;
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


   private boolean accessesChanged(ProofMetaPerTypeReferences ptRefs) {
      for (ProofMetaReferenceAccess access : ptRefs.getAccesses()) {
         if(accessChanged(access)){
            return true;
         }
      }
      return false;
   }


   private boolean accessChanged(ProofMetaReferenceAccess access) {
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(access.getKjt());
      if (kjt != null) {
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
         List<Pair<KeYJavaType, IProgramMethod>> implementations = KeYResourcesUtil.getKjtsOfAllImplementations(env, kjt, callMethod.getName(), callMethod.getParameters());
         String implementationsString = KeYResourcesUtil.implementationTypesToString(implementations);
         String[] refSplits = callMethod.getImplementations().split(";");
         String[] envSplits = implementationsString.split(";");
         if(refSplits.length == envSplits.length) {
            for(String refSplit : refSplits) {
               boolean found = false;
               for(String envSplit : envSplits) {
                  if(envSplit.equals(refSplit)) {
                     found = true;
                  }
               }
               if(!found) {
                  return true;
               }
            }
            return false;
         }
      }
      return true;
   }


   private boolean inlineMethodsChanged(ProofMetaPerTypeReferences ptRefs) {
      for (ProofMetaReferenceMethod inlineMethod : ptRefs.getInlineMethods()) {
         if (inlineMethodChanged(inlineMethod)) {
            return true;
         }
      }
      return false;
   }
   
   
   private boolean inlineMethodChanged(ProofMetaReferenceMethod method) {
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(method.getKjt());
      if(kjt != null){
         IProgramMethod pm = KeYResourcesUtil.getMethodForKjt(kjt, method.getName(), method.getParameters());
         if(pm != null){
            String src = KeYResourcesUtil.createSourceString(pm.getMethodDeclaration());
            if (method.getSource().equals(src)) {
               return false;
            }
         }
      }
      return true;
   }


   private boolean contractsChanged(ProofMetaPerTypeReferences ptRefs) {
      for (ProofMetaReferenceContract contract : ptRefs.getContracts()) {
         Contract c = env.getSpecificationRepository().getContractByName(contract.getName());
         if (c == null || !contract.getContract().equals(c.toString()) || !contract.getKjt().equals(c.getKJT().getFullName())) {
            return true;
         }
      }
      return false;
   }

}
