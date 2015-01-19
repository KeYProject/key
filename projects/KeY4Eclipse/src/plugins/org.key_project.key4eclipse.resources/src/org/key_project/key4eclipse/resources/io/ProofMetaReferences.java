package org.key_project.key4eclipse.resources.io;

import java.io.IOException;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public class ProofMetaReferences {

   private String contract;
   private List<ProofMetaReferenceAxiom> axioms;
   private List<ProofMetaReferenceInvariant> invariants;
   private List<ProofMetaReferenceAccess> accesses;
   private List<ProofMetaReferenceCallMethod> callMethods;
   private List<ProofMetaReferenceMethod> inlineMethods;
   private List<ProofMetaReferenceContract> contracts;
   
   public ProofMetaReferences(){
      this.contract = null;
      this.axioms = new LinkedList<ProofMetaReferenceAxiom>();
      this.invariants = new LinkedList<ProofMetaReferenceInvariant>();
      this.accesses = new LinkedList<ProofMetaReferenceAccess>();
      this.callMethods = new LinkedList<ProofMetaReferenceCallMethod>();
      this.inlineMethods = new LinkedList<ProofMetaReferenceMethod>();
      this.contracts = new LinkedList<ProofMetaReferenceContract>();
   }
      
   public void createFromProofElement(ProofElement pe, KeYEnvironment<?> env) {
      contract = contractToString(pe.getContract());
      List<IProofReference<?>> references = KeYResourcesUtil.sortProofReferences(KeYResourcesUtil.filterProofReferences(pe.getProofReferences()), IProofReference.USE_AXIOM, IProofReference.USE_INVARIANT, IProofReference.ACCESS, IProofReference.CALL_METHOD, IProofReference.INLINE_METHOD, IProofReference.USE_CONTRACT);
      for(IProofReference<?> proofRef : references){
         if(IProofReference.USE_AXIOM.equals(proofRef.getKind())){
            createAxiom((ClassAxiom) proofRef.getTarget());
         }
         else if(IProofReference.USE_INVARIANT.equals(proofRef.getKind())){
            createInvariant((ClassInvariant) proofRef.getTarget());
         }
         else if(IProofReference.ACCESS.equals(proofRef.getKind())){
            IProgramMethod target = null;
            if(pe.getContract().getTarget() instanceof IProgramMethod) {
               target = (IProgramMethod) pe.getContract().getTarget();
            }
            createAccess((IProgramVariable) proofRef.getTarget(), env, target);
         }
         else if(IProofReference.CALL_METHOD.equals(proofRef.getKind())){
            IProgramMethod programMethod = (IProgramMethod) proofRef.getTarget();
            createCallMethod(programMethod, env);
         }
         else if(IProofReference.INLINE_METHOD.equals(proofRef.getKind())){
            IProgramMethod programMethod = (IProgramMethod) proofRef.getTarget();
            createInlineMethod(programMethod);
         }
         else if(IProofReference.USE_CONTRACT.equals(proofRef.getKind())){
            Contract c = (Contract) proofRef.getTarget();
            String name = c.getName();
            if(!containsContract(name)){
               contracts.add(new ProofMetaReferenceContract(name, contractToString(c)));
            }
         }
      }
   }

   private void createAxiom(ClassAxiom axiom) {
      if(axiom instanceof RepresentsAxiom){
         RepresentsAxiom repAxiom = (RepresentsAxiom) axiom;
         KeYJavaType kjt = repAxiom.getKJT();
         axioms.add(new ProofMetaReferenceAxiom(kjt.getFullName(), repAxiom.getName(), repAxiomToString(repAxiom)));
      }
   }

   private void createInvariant(ClassInvariant invariant) {
      KeYJavaType kjt = invariant.getKJT();
      invariants.add(new ProofMetaReferenceInvariant(kjt.getFullName(), invariant.getName(), invariantToString(invariant)));
   }
   
   private void createAccess(IProgramVariable variable, KeYEnvironment<?> env, IProgramMethod target) {
      KeYJavaType kjt = null;
      String name = variable.name().toString();
      if(variable instanceof ProgramVariable) {
         ProgramVariable pv = (ProgramVariable) variable;
         kjt = pv.getContainerType();
         if(kjt != null && !containsAccess(kjt.getFullName(), name)){
            FieldDeclaration fieldDecl = KeYResourcesUtil.getFieldDeclFromKjt(kjt, name);
            if(fieldDecl != null) {
               String type = fieldDecl.getTypeReference().toString();
               String visibility = "";
               VisibilityModifier vm = fieldDecl.getVisibilityModifier();
               if(vm != null) {
                  visibility = vm.toString();
               }
               boolean isStatic = fieldDecl.isStatic();
               boolean isFinal = fieldDecl.isFinal();
               boolean isCalledInConstructor = target.isConstructor();//TODO how to find out if this variable is set in a constructor??
               String initializer =  "";
               if(isStatic || isFinal) {
                  initializer = fieldDecl.getFieldSpecifications().get(0).getInitializer().toString();
               }
               accesses.add(new ProofMetaReferenceAccess(kjt.getFullName(), name, type, visibility, isStatic, isFinal, isCalledInConstructor, initializer));
            }
         }
      }
   }
   
   private void createCallMethod(IProgramMethod programMethod, KeYEnvironment<?> env) {
      KeYJavaType kjt = programMethod.getContainerType();
      MethodDeclaration methodDecl = programMethod.getMethodDeclaration();
      String name = methodDecl.getFullName();
      if(name.indexOf("<") == -1 || name.indexOf("<init>") >= 0){
         String parameters = KeYResourcesUtil.parametersToString(methodDecl.getParameters());
         if(!containsCallMethod(kjt.getFullName(), name, parameters)){
            Map<KeYJavaType, IProgramMethod> implementations = KeYResourcesUtil.getKjtsOfAllImplementations(env, kjt, name, parameters);
            String implementationsString = KeYResourcesUtil.implementationTypesToString(implementations);
            callMethods.add(new ProofMetaReferenceCallMethod(kjt.getFullName(), name, parameters, implementationsString));
            for(Map.Entry<KeYJavaType, IProgramMethod> implementation : implementations.entrySet()) {
               List<IProgramMethod> overloads = findOverloads(implementation.getValue(), env);
               for(IProgramMethod pm : overloads) {
                  createInlineMethod(pm);
               }
            }
         }
      }
   }

   private void createInlineMethod(IProgramMethod programMethod){
      KeYJavaType kjt = programMethod.getContainerType();
      MethodDeclaration methodDecl = programMethod.getMethodDeclaration();
      String name = methodDecl.getFullName();
      if(name.indexOf("<") == -1 || name.indexOf("<init>") >= 0){
         String methodParameters = KeYResourcesUtil.parametersToString(methodDecl.getParameters());
         if(!containsMethod(kjt.getFullName(), name, methodParameters)){
            String src = KeYResourcesUtil.createSourceString(methodDecl);
            inlineMethods.add(new ProofMetaReferenceMethod(kjt.getFullName(), name, methodParameters, src));
         }
      }
   }   
   
   private List<IProgramMethod> findOverloads(IProgramMethod programMethod, KeYEnvironment<?> env){
      List<IProgramMethod> overloads = new LinkedList<IProgramMethod>();
      KeYJavaType kjt = programMethod.getContainerType();
      if(kjt != null && kjt.getJavaType() instanceof TypeDeclaration) {
         TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
         for(MemberDeclaration memberDecl : typeDecl.getMembers()) {
            if (memberDecl instanceof IProgramMethod) {
               IProgramMethod pm = (IProgramMethod) memberDecl;
               if (pm.getFullName().equals(programMethod.getFullName()) && isSubtypeOverloading(programMethod, pm, env)) {
                  overloads.add(pm);
               }
            }
         }
      }
      return overloads;
   }
   
   private boolean isSubtypeOverloading(IProgramMethod base, IProgramMethod overload, KeYEnvironment<?> env){
      if(base.getParameterDeclarationCount() == overload.getParameterDeclarationCount()) {
         for(int i = 0; i < base.getParameterDeclarationCount(); i++) {
            ParameterDeclaration baseParameter = base.getParameterDeclarationAt(i);
            KeYJavaType baseType = baseParameter.getTypeReference().getKeYJavaType();
            ParameterDeclaration overloadParameter = overload.getParameterDeclarationAt(i);
            KeYJavaType overloadType = overloadParameter.getTypeReference().getKeYJavaType();
            if(!baseType.equals(overloadType) && !env.getJavaInfo().getAllSubtypes(baseType).contains(overloadType)){
               return false;
            }
         }
         return true;
      }
      return false;
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
   
   private boolean containsContract(String name){
      for(ProofMetaReferenceContract contract : contracts){
         if(name.equals(contract.getName())){
            return true;
         }
      }
      return false;
   }

   private String contractToString(Contract c) {
      return c.toString();
   }
   private String repAxiomToString(RepresentsAxiom a) {
      return a.toString();
   }
   private String invariantToString(ClassInvariant i){
      return i.getOriginalInv().toString();
   }

   public String getContract() {
      return contract;
   }
   public void setContract(String contract) {
      this.contract = contract;
   }

   public List<ProofMetaReferenceAxiom> getAxioms() {
      return axioms;
   }
   public void addAxiom(ProofMetaReferenceAxiom axiom){
      axioms.add(axiom);
   }

   public List<ProofMetaReferenceInvariant> getInvariants() {
      return invariants;
   }
   public void addInvariant(ProofMetaReferenceInvariant invariant){
      invariants.add(invariant);
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
