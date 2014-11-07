package org.key_project.key4eclipse.resources.io;

import java.io.IOException;
import java.io.StringWriter;
import java.util.LinkedList;
import java.util.List;

import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public class ProofMetaReferences {

   private String contract;
   private ProofMetaReferenceAxiom axiom;
   private ProofMetaReferenceInvariant invariant;
   private List<ProofMetaReferenceAccess> accesses;
   private List<ProofMetaReferenceCallMethod> callMethods;
   private List<ProofMetaReferenceMethod> inlineMethods;
   private List<ProofMetaReferenceContract> contracts;
   
   public ProofMetaReferences(){
      this.contract = null;
      this.axiom = null;
      this.invariant = null;
      this.accesses = new LinkedList<ProofMetaReferenceAccess>();
      this.callMethods = new LinkedList<ProofMetaReferenceCallMethod>();
      this.inlineMethods = new LinkedList<ProofMetaReferenceMethod>();
      this.contracts = new LinkedList<ProofMetaReferenceContract>();
   }
      
   public void createFromProofElement(ProofElement pe, KeYEnvironment<?> env) {
      contract = pe.getContract().toString();
      List<IProofReference<?>> references = KeYResourcesUtil.sortProofReferences(KeYResourcesUtil.filterProofReferences(pe.getProofReferences()), IProofReference.USE_AXIOM, IProofReference.USE_INVARIANT, IProofReference.ACCESS, IProofReference.CALL_METHOD, IProofReference.INLINE_METHOD, IProofReference.USE_CONTRACT);
      for(IProofReference<?> proofRef : references){
         if(IProofReference.USE_AXIOM.equals(proofRef.getKind())){
            ClassAxiom classAxiom = (ClassAxiom) proofRef.getTarget();
            if(classAxiom instanceof RepresentsAxiom){
               RepresentsAxiom repAxiom = (RepresentsAxiom) classAxiom;
               KeYJavaType kjt = repAxiom.getKJT();
               axiom = new ProofMetaReferenceAxiom(kjt.getFullName(), repAxiom.getName(), repAxiom.toString());
            }
         }
         else if(IProofReference.USE_INVARIANT.equals(proofRef.getKind())){
            ClassInvariant classInvariant = (ClassInvariant) proofRef.getTarget();
            KeYJavaType kjt = classInvariant.getKJT();
            invariant = new ProofMetaReferenceInvariant(kjt.getFullName(), classInvariant.getName(), classInvariant.getOriginalInv().toString());
         }
         else if(IProofReference.ACCESS.equals(proofRef.getKind())){
            IProgramVariable v = (IProgramVariable) proofRef.getTarget();
            KeYJavaType kjt = null;
            if(v instanceof LocationVariable){
               LocationVariable lv = (LocationVariable) v;
               kjt = lv.getContainerType();
            }
            else if(v instanceof ProgramConstant){
               ProgramConstant pc = (ProgramConstant) v;
               kjt = pc.getContainerType();
            }
            if(kjt != null){
               Type type = kjt.getJavaType();
               if(type instanceof TypeDeclaration){
                  TypeDeclaration typeDecl = (TypeDeclaration) type;
                  for(MemberDeclaration memberDecl : typeDecl.getMembers()){
                     if(memberDecl instanceof FieldDeclaration){
                        FieldDeclaration fieldDecl = (FieldDeclaration) memberDecl;
                        ImmutableArray<FieldSpecification> fieldSpecs = fieldDecl.getFieldSpecifications();
                        if(fieldSpecs.size() == 1){
                           FieldSpecification fieldSpec = fieldSpecs.get(0);
                           if(v.equals(fieldSpec.getProgramVariable()) && !containsAccess(kjt.getFullName(), fieldSpec.getName())){
                              accesses.add(new ProofMetaReferenceAccess(kjt.getFullName(), fieldSpec.getName(), fieldSpec.toString()));
                           }
                        }
                        else{
                           try {
                              throw new Exception("No or more than one fieldSpecificaion found for " + v.toString());
                           }
                           catch (Exception e) {
                              // TODO: what to do when this happens? can this happen??
                              e.printStackTrace();
                           }
                        }
                     }
                  }
               }
            }
         }
         else if(IProofReference.CALL_METHOD.equals(proofRef.getKind())){
            IProgramMethod programMethod = (IProgramMethod) proofRef.getTarget();
            KeYJavaType kjt = programMethod.getContainerType();
            MethodDeclaration methodDecl = programMethod.getMethodDeclaration();
            String name = methodDecl.getFullName();
            if(name.indexOf("<") == -1 || name.indexOf("<init>") >= 0){
               String parameters = KeYResourcesUtil.parametersToString(methodDecl.getParameters());
               ImmutableList<KeYJavaType> subTypes = env.getJavaInfo().getAllSubtypes(kjt);
               List<ProofMetaReferenceMethod> subMethods = createSubMethods(subTypes, name, parameters);
               if(!containsCallMethod(kjt.getFullName(), name, parameters)){
                  StringWriter sw = new StringWriter();
                  try{
                     ProofMetaReferencesPrettyPrinter pp = new ProofMetaReferencesPrettyPrinter(sw, true);
                     pp.printMethodDeclaration(methodDecl);
                  }
                  catch (IOException e){
                     LogUtil.getLogger().logError(e);
                  }
                  String src = sw.toString();
                  src = KeYResourcesUtil.removeLineBreaks(src);
                  callMethods.add(new ProofMetaReferenceCallMethod(kjt.getFullName(), name, parameters, src, subMethods));
               }
            }
         }
         else if(IProofReference.INLINE_METHOD.equals(proofRef.getKind())){
            IProgramMethod programMethod = (IProgramMethod) proofRef.getTarget();
            KeYJavaType kjt = programMethod.getContainerType();
            MethodDeclaration methodDecl = programMethod.getMethodDeclaration();
            String name = methodDecl.getFullName();
            if(name.indexOf("<") == -1 || name.indexOf("<init>") >= 0){
               String methodParameters = KeYResourcesUtil.parametersToString(methodDecl.getParameters());
               if(!containsMethod(kjt.getFullName(), name, methodParameters) && !containsCallMethodOrSubImplementation(kjt.getFullName(), name, methodParameters)){
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
                  inlineMethods.add(new ProofMetaReferenceMethod(kjt.getFullName(), name, methodParameters, src));
               }
            }
         }
         else if(IProofReference.USE_CONTRACT.equals(proofRef.getKind())){
            Contract c = (Contract) proofRef.getTarget();
            String name = c.getName();
            if(!containsContract(name)){
               contracts.add(new ProofMetaReferenceContract(name, c.toString()));
            }
         }
      }
   }
   
   
   private List<ProofMetaReferenceMethod> createSubMethods(ImmutableList<KeYJavaType> subKjts, String refName, String refParameters) {
      List<ProofMetaReferenceMethod> subMethods = new LinkedList<ProofMetaReferenceMethod>();
      for(KeYJavaType kjt : subKjts){
         Type type = kjt.getJavaType();
         if(type instanceof TypeDeclaration){
            TypeDeclaration typeDecl = (TypeDeclaration) type;
            for(MemberDeclaration memberDecl : typeDecl.getMembers()){
               if(memberDecl instanceof IProgramMethod){
                  IProgramMethod pmethod = (IProgramMethod) memberDecl;
                  MethodDeclaration methodDecl = pmethod.getMethodDeclaration();
                  String name = methodDecl.getFullName();
                  String parameters = KeYResourcesUtil.parametersToString(methodDecl.getParameters());
                  if(refName.equals(name) && refParameters.equals(parameters)){
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
                     subMethods.add(new ProofMetaReferenceMethod(kjt.getFullName(), name, parameters, src));
                  }
               }
            }
         }
      }
      return subMethods;
   }
   
   
   private boolean containsAccess(String kjt, String name){
      for(ProofMetaReferenceAccess access : accesses){
         if(kjt.equals(access.getKjt()) && name.equals(access.getName())){
            return true;
         }
      }
      return false;
   }
   
   private boolean containsMethod(String kjt, String methodName, String parameters){
      for(ProofMetaReferenceMethod method : inlineMethods){
         if(method.getKjt().equals(kjt) && method.getName().equals(methodName) && method.getParameters().equals(parameters)){
            return true;
         }
      }
      return false;
   }
   
   private boolean containsCallMethod(String kjt, String methodName, String parameters){
      for(ProofMetaReferenceCallMethod method : callMethods){
         if(method.getKjt().equals(kjt) && method.getName().equals(methodName) && method.getParameters().equals(parameters)){
            return true;
         }
      }
      return false;
   }
   
   private boolean containsCallMethodOrSubImplementation(String kjt, String methodName, String parameters) {
      for(ProofMetaReferenceCallMethod method : callMethods){
         if(method.getKjt().equals(kjt) && method.getName().equals(methodName) && method.getParameters().equals(parameters)){
            return true;
         }
         else {
            for(ProofMetaReferenceMethod subImpl : method.getSubImpl()) {
               if(subImpl.getKjt().equals(kjt) && subImpl.getName().equals(methodName) && subImpl.getParameters().equals(parameters)){
                  return true;
               }
            }
         }
      }
      return false;
   }
   
   private boolean containsContract(String name){
      for(ProofMetaReferenceContract contract : contracts){
         if(name.equals(contract.getName())){
            return true;
         }
      }
      return false;
   }

   public String getContract() {
      return contract;
   }
   public void setContract(String contract) {
      this.contract = contract;
   }

   public ProofMetaReferenceAxiom getAxiom() {
      return axiom;
   }
   public void setAxiom(ProofMetaReferenceAxiom axiom){
      this.axiom = axiom;
   }

   public ProofMetaReferenceInvariant getInvariant() {
      return invariant;
   }
   public void setInvariant(ProofMetaReferenceInvariant invariant){
      this.invariant = invariant;
   }

   public List<ProofMetaReferenceAccess> getAccesses() {
      return accesses;
   }
   public void addAccess(ProofMetaReferenceAccess access){
      accesses.add(access);
   }

   public List<ProofMetaReferenceCallMethod> getCallMethods() {
      return callMethods;
   }
   public void addCallMethod(ProofMetaReferenceCallMethod callMethod) {
      callMethods.add(callMethod);
   }

   public List<ProofMetaReferenceMethod> getInlineMethods() {
      return inlineMethods;
   }
   public void addInlineMethod(ProofMetaReferenceMethod inlineMethod) {
      inlineMethods.add(inlineMethod);
   }

   public List<ProofMetaReferenceContract> getContracts() {
      return contracts;
   }
   public void addContract(ProofMetaReferenceContract contract) {
     contracts.add(contract);
   }
   
}
