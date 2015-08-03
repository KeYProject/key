package org.key_project.key4eclipse.resources.io;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.RepresentsAxiom;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;

/**
 * Creates the representation of all references used by a particular {@link ProofElement}
 * @author Stefan Käsdorf
 */
public class ProofMetaReferences {

   private String contract;
   private Map<String, ProofMetaPerTypeReferences> perTypeReferences;
   private List<ProofMetaReferenceCallMethod> callMethods;


   public ProofMetaReferences(){
      this.contract = null;
      this.perTypeReferences = new LinkedHashMap<String, ProofMetaPerTypeReferences>();
      this.callMethods = new LinkedList<ProofMetaReferenceCallMethod>();
   }
   
   public ProofMetaReferences(ProofElement pe, Set<IProofReference<?>> proofReferences){
      this.contract = null;
      this.perTypeReferences = new LinkedHashMap<String, ProofMetaPerTypeReferences>();
      this.callMethods = new LinkedList<ProofMetaReferenceCallMethod>();
      createFromProofElement(pe, proofReferences);
   }
   
   
   /**
    * Creates the {@link ProofMetaReferences} from a {@link ProofElement}
    * @param pe the {@link ProofElement} to use
    * @param env the {@link KeYEnvironment} to use
    */
   public void createFromProofElement(ProofElement pe, Set<IProofReference<?>> proofReferences) {
      KeYEnvironment<?> env = pe.getKeYEnvironment();
      contract = KeYResourcesUtil.contractToString(pe.getContract());
      List<IProofReference<?>> sortedReferences = KeYResourcesUtil.sortProofReferences(proofReferences, IProofReference.USE_AXIOM, IProofReference.USE_INVARIANT, IProofReference.ACCESS, IProofReference.CALL_METHOD, IProofReference.INLINE_METHOD, IProofReference.USE_CONTRACT);
      for(IProofReference<?> proofRef : sortedReferences){
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
            String kjt = c.getKJT().getFullName();
            String name = c.getName();
            ProofMetaPerTypeReferences ptRefs = getPerTypeReferences(kjt);
            if(!containsContract(kjt, name, ptRefs)){
               ptRefs.addContract(new ProofMetaReferenceContract(kjt, name, KeYResourcesUtil.contractToString(c)));
            }
         }
      }
   }
   
   public ProofMetaPerTypeReferences getPerTypeReferences(String kjt){
      ProofMetaPerTypeReferences ptRefs = perTypeReferences.get(kjt);
      if(ptRefs == null){
         ptRefs = new ProofMetaPerTypeReferences();
         perTypeReferences.put(kjt, ptRefs);
      }
      return ptRefs;
   }

   private void createAxiom(ClassAxiom axiom) {
      if(axiom instanceof RepresentsAxiom){
         RepresentsAxiom repAxiom = (RepresentsAxiom) axiom;
         String kjt = repAxiom.getKJT().getFullName();
         ProofMetaPerTypeReferences ptRefs = getPerTypeReferences(kjt);
         ptRefs.addAxiom(new ProofMetaReferenceAxiom(kjt, repAxiom.getName(), KeYResourcesUtil.repAxiomToString(repAxiom)));
      }
   }

   private void createInvariant(ClassInvariant invariant) {
      String kjt = invariant.getKJT().getFullName();
      ProofMetaPerTypeReferences ptRefs = getPerTypeReferences(kjt);
      ptRefs.addInvariant(new ProofMetaReferenceInvariant(kjt, invariant.getName(), KeYResourcesUtil.invariantToString(invariant)));
   }
   
   private void createAccess(IProgramVariable variable, KeYEnvironment<?> env, IProgramMethod target) {
      KeYJavaType kjt = null;
      String name = variable.name().toString();
      if(variable instanceof ProgramVariable) {
         ProgramVariable pv = (ProgramVariable) variable;
         kjt = pv.getContainerType();
         ProofMetaPerTypeReferences ptRefs = getPerTypeReferences(kjt.getFullName());
         if(kjt != null && !containsAccess(kjt.getFullName(), name, ptRefs)){
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
               String initializer =  "";
               if(isFinal) {
                  initializer = fieldDecl.getFieldSpecifications().get(0).getInitializer().toString();
               }
               ptRefs.addAccess(new ProofMetaReferenceAccess(kjt.getFullName(), name, type, visibility, isStatic, isFinal, initializer));
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
            List<Pair<KeYJavaType, IProgramMethod>> implementations = KeYResourcesUtil.getKjtsOfAllImplementations(env, kjt, name, parameters);
            String implementationsString = KeYResourcesUtil.implementationTypesToString(implementations);
            callMethods.add(new ProofMetaReferenceCallMethod(kjt.getFullName(), name, parameters, implementationsString));
            for(Pair<KeYJavaType, IProgramMethod> implementation : implementations) {
//               List<IProgramMethod> overloads = findOverloads(implementation.getValue(), env);
//               for(IProgramMethod pm : overloads) {
//                  createInlineMethod(pm);
//               }
               createInlineMethod(implementation.second);
            }
         }
      }
   }

   private void createInlineMethod(IProgramMethod programMethod){
      String kjt = programMethod.getContainerType().getFullName();
      MethodDeclaration methodDecl = programMethod.getMethodDeclaration();
      String name = methodDecl.getFullName();
      if(name.indexOf("<") == -1 || name.indexOf("<init>") >= 0){
         String methodParameters = KeYResourcesUtil.parametersToString(methodDecl.getParameters());
         ProofMetaPerTypeReferences ptRefs = getPerTypeReferences(kjt);
         if(!containsMethod(kjt, name, methodParameters, ptRefs)){
            String src = KeYResourcesUtil.createSourceString(methodDecl);
            ptRefs.addInlineMethod(new ProofMetaReferenceMethod(kjt, name, methodParameters, src));
         }
      }
   }   
   
//   private List<IProgramMethod> findOverloads(IProgramMethod programMethod, KeYEnvironment<?> env){
//      List<IProgramMethod> overloads = new LinkedList<IProgramMethod>();
//      KeYJavaType kjt = programMethod.getContainerType();
//      if(kjt != null && kjt.getJavaType() instanceof TypeDeclaration) {
//         TypeDeclaration typeDecl = (TypeDeclaration) kjt.getJavaType();
//         for(MemberDeclaration memberDecl : typeDecl.getMembers()) {
//            if (memberDecl instanceof IProgramMethod) {
//               IProgramMethod pm = (IProgramMethod) memberDecl;
//               if (pm.getFullName().equals(programMethod.getFullName()) && isSubtypeOverloading(programMethod, pm, env)) {
//                  overloads.add(pm);
//               }
//            }
//         }
//      }
//      return overloads;
//   }
//   
//   private boolean isSubtypeOverloading(IProgramMethod base, IProgramMethod overload, KeYEnvironment<?> env){
//      if(base.getParameterDeclarationCount() == overload.getParameterDeclarationCount()) {
//         for(int i = 0; i < base.getParameterDeclarationCount(); i++) {
//            ParameterDeclaration baseParameter = base.getParameterDeclarationAt(i);
//            KeYJavaType baseType = baseParameter.getTypeReference().getKeYJavaType();
//            ParameterDeclaration overloadParameter = overload.getParameterDeclarationAt(i);
//            KeYJavaType overloadType = overloadParameter.getTypeReference().getKeYJavaType();
//            if(!baseType.equals(overloadType) && !env.getJavaInfo().getAllSubtypes(baseType).contains(overloadType)){
//               return false;
//            }
//         }
//         return true;
//      }
//      return false;
//   }
   
   private boolean containsAccess(String kjt, String name, ProofMetaPerTypeReferences ptRefs){
      if(ptRefs != null){
         for(ProofMetaReferenceAccess access : ptRefs.getAccesses()){
            if(kjt.equals(access.getKjt()) && name.equals(access.getName())){
               return true;
            }
         }
      }
      return false;
   }
   
   private boolean containsMethod(String kjt, String methodName, String parameters, ProofMetaPerTypeReferences ptRefs){
      if(ptRefs != null){
         for(ProofMetaReferenceMethod method : ptRefs.getInlineMethods()){
            if(method.getKjt().equals(kjt) && method.getName().equals(methodName) && method.getParameters().equals(parameters)){
               return true;
            }
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
   
   private boolean containsContract(String kjt, String name, ProofMetaPerTypeReferences ptRefs){
      if(ptRefs != null){
         for(ProofMetaReferenceContract contract : ptRefs.getContracts()){
            if(kjt.equals(contract.getKjt()) && name.equals(contract.getName())){
               return true;
            }
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
   
   public Map<String, ProofMetaPerTypeReferences> getPerTypeReferences() {
      return perTypeReferences;
   }

   public List<ProofMetaReferenceCallMethod> getCallMethods() {
      return callMethods;
   }
   public void addCallMethod(ProofMetaReferenceCallMethod callMethod) {
      callMethods.add(callMethod);
   }
}
