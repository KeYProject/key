package org.key_project.key4eclipse.resources.io;

import java.io.IOException;
import java.io.StringWriter;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public class ProofMetaReferencesComparator {

   private ProofElement pe;
   private ProofMetaReferences references;
   private KeYEnvironment<?> env;
   
   public ProofMetaReferencesComparator(ProofElement pe, KeYEnvironment<?> env) {
      this.pe = pe;
      this.references = pe.getProofMetaReferences();
      this.env = env;
   }

   
   public boolean compareReferences() {
      if(references != null){
         if (!(contractChanged() || axiomChanged() || invariantChanged() || accessesChanged() || callMethodsChanged() || inlineMethodsChanged() || contractsChanged())) {
            return false;
         }
      }
      return true;
   }


   private boolean contractChanged() {
      if (pe.getContract().toString().equals(references.getContract())) {
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
               ImmutableSet<ClassAxiom> classAxioms = env.getSpecificationRepository().getClassAxioms(kjt);
               for(ClassAxiom classAxiom : classAxioms) {
                  if(classAxiom instanceof RepresentsAxiom && classAxiom.getName().equals(axiom.getName())) {
                     RepresentsAxiom repAxiom = (RepresentsAxiom) classAxiom;
                     if(!axiom.getOriginalRep().equals(repAxiom.toString())){
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


   private boolean invariantChanged() {
      List<ProofMetaReferenceInvariant> invariants = references.getInvariants();
      for(ProofMetaReferenceInvariant invariant : invariants){
         if (invariant != null) {
            KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(invariant.getKjt());
            if (kjt != null) {
               ImmutableSet<ClassInvariant> classInvariants = env.getSpecificationRepository().getClassInvariants(kjt);
               for(ClassInvariant classInvariant : classInvariants) {
                  if(classInvariant.getName().equals(invariant.getName()) && !invariant.getOriginalInv().equals(classInvariant.getOriginalInv().toString())) {
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
         FieldDeclaration fieldDecl = KeYResourcesUtil.getFieldDeclFromKjt(kjt, access.getName());
         if(fieldDecl != null) {
            String type = fieldDecl.getTypeReference().toString();
            String visibility = "";
            VisibilityModifier vm = fieldDecl.getVisibilityModifier();
            if(vm != null) {
               visibility = vm.toString();
            }
            boolean isStatic = fieldDecl.isStatic();
            boolean isFinal = fieldDecl.isFinal();
            IObserverFunction target = pe.getContract().getTarget();
            boolean isCalledInConstructor = target instanceof IProgramMethod ? ((IProgramMethod) target).isConstructor() : false;
            if(type.equals(access.getType()) && visibility.equals(access.getVisibility()) 
                  && isStatic == access.isStatic() && isFinal == access.isFinal() && isCalledInConstructor == access.isCalledInConstructor()) {
               if(isStatic || isFinal || isCalledInConstructor) {
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
      Map<KeYJavaType, IProgramMethod> implementations = KeYResourcesUtil.getKjtsOfAllImplementations(env, kjt, callMethod.getName(), callMethod.getParameters());
      String implementationsString = KeYResourcesUtil.implementationTypesToString(implementations);
      if(implementationsString.equals(callMethod.getImplementations())) {
         return false;
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
      IProgramMethod pm = KeYResourcesUtil.getMethodForKjt(kjt, method.getName(), method.getParameters());
      if(pm != null){
         String src = KeYResourcesUtil.createSourceString(pm.getMethodDeclaration());
         if (method.getSource().equals(src)) {
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
