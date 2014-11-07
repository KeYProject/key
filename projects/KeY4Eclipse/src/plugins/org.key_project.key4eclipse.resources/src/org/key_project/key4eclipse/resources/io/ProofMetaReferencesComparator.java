package org.key_project.key4eclipse.resources.io;

import java.io.IOException;
import java.io.StringWriter;
import java.util.LinkedList;
import java.util.List;

import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
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
      ProofMetaReferenceAxiom axiom = references.getAxiom();
      if(axiom != null){
         KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(axiom.getKjt());
         if(kjt != null){
            ImmutableSet<ClassAxiom> classAxioms = env.getSpecificationRepository().getClassAxioms(kjt);
            for(ClassAxiom classAxiom : classAxioms) {
               if(classAxiom instanceof RepresentsAxiom && classAxiom.getName().equals(axiom.getName())) {
                  RepresentsAxiom repAxiom = (RepresentsAxiom) classAxiom;
                  return !axiom.getOriginalRep().equals(repAxiom.toString());
               }
            }
         }
         return true;
      }
      return false;
   }


   private boolean invariantChanged() {
      ProofMetaReferenceInvariant invariant = references.getInvariant();
      if (invariant != null) {
         KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(invariant.getKjt());
         if (kjt != null) {
            ImmutableSet<ClassInvariant> classInvariants = env.getSpecificationRepository().getClassInvariants(kjt);
            for(ClassInvariant classInvariant : classInvariants) {
               if(classInvariant.getName().equals(invariant.getName()) && invariant.getOriginalInv().equals(classInvariant.getOriginalInv().toString())) {
                  return false;
               }
            }
         }
         return true;
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
      if (kjt != null && kjt.getJavaType() instanceof TypeDeclaration) {
         TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
         ImmutableList<Field> fields = env.getJavaInfo().getAllFields(typeDecl);
         for (Field field : fields) {
            if(access.getName().equals(field.getName()) && access.getSource().equals(field.toString())) {
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
      if (!methodChanged(callMethod, true)) {
         return subImplementationsChanged(callMethod.getSubImpl(), getAllSubMethodsFromEnv(callMethod));
      }
      return true;
   }
   
   private List<IProgramMethod> getAllSubMethodsFromEnv(ProofMetaReferenceCallMethod callMethod){
      List<IProgramMethod> subMethodList = new LinkedList<IProgramMethod>();
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(callMethod.getKjt());
      ImmutableList<KeYJavaType> subTypes = env.getJavaInfo().getAllSubtypes(kjt);
      for (KeYJavaType subType : subTypes) {
         if (subType.getJavaType() instanceof TypeDeclaration) {
            TypeDeclaration typeDecl = (TypeDeclaration) subType.getJavaType();
            for (MemberDeclaration memberDecl : typeDecl.getMembers()) {
               if (memberDecl instanceof IProgramMethod) {
                  IProgramMethod pm = (IProgramMethod) memberDecl;
                  MethodDeclaration md = pm.getMethodDeclaration();
                  if (md.getName().equals(callMethod.getName()) 
                        && callMethod.getParameters().equals(KeYResourcesUtil.parametersToString(md.getParameters()))){
                     subMethodList.add(pm);
                  }
               }
            }
         }
      }
      return subMethodList;
   }


   private boolean subImplementationsChanged(List<ProofMetaReferenceMethod> subImpl, List<IProgramMethod> envSubMethods) {
      for (ProofMetaReferenceMethod subMethod : subImpl) {
         for (IProgramMethod pm : envSubMethods) {
            if(subMethod.getKjt().equals(pm.getContainerType().getFullName())) {
               envSubMethods.remove(pm);
               break;
            }
         }
         if (methodChanged(subMethod, true)) {
            return true;
         }
      }
      if (!envSubMethods.isEmpty()) {
         return true;
      }
      return false;
   }


   private boolean inlineMethodsChanged() {
      for (ProofMetaReferenceMethod inlineMethod : references.getInlineMethods()) {
         if (methodChanged(inlineMethod, false)) {
            return true;
         }
      }
      return false;
   }
   
   
   private boolean methodChanged(ProofMetaReferenceMethod method, boolean callmethod) {
      KeYJavaType kjt = env.getJavaInfo().getKeYJavaType(method.getKjt());
      if (kjt != null && kjt.getJavaType() instanceof TypeDeclaration) {
         TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
         for (MemberDeclaration memberDecl : typeDecl.getMembers()) {
            if (memberDecl instanceof IProgramMethod) {
               IProgramMethod pm = (IProgramMethod) memberDecl;
               MethodDeclaration md = pm.getMethodDeclaration();
               if (md.getName().equals(method.getName()) && KeYResourcesUtil.parametersToString(md.getParameters()).equals(method.getParameters())) {
                  StringWriter sw = new StringWriter();
                  try{
                     ProofMetaReferencesPrettyPrinter pp = new ProofMetaReferencesPrettyPrinter(sw, true);
                     if (!callmethod) {
                        pp.printInlineMethodDeclaration(md);
                     }
                     else {
                        pp.printMethodDeclaration(md);
                     }
                  }
                  catch (IOException e){
                     LogUtil.getLogger().logError(e);
                  }
                  String src = sw.toString();
                  src = KeYResourcesUtil.removeLineBreaks(src);
                  if (method.getSource().equals(src)) {
                     return false;
                  }
               }
            }
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
