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

package org.key_project.key4eclipse.resources.io;

import java.io.ByteArrayInputStream;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourceAttributes;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.XMLUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Writer for the meta files.
 * @author Stefan Käsdorf
 */
public class ProofMetaFileWriter {
   public static final String TAG_PROOF_META_FILE = "proofMetaFile";
   public static final String TAG_USED_TYPES = "usedTypes";
   public static final String TAG_TYPE = "type";
   public static final String TAG_SUB_TYPE = "subType";
   public static final String TAG_USED_CONTRACTS = "usedContracts";
   public static final String TAG_USED_CONTRACT = "usedContract";
   public static final String TAG_ASSUMPTIONS = "assumptions";
   public static final String TAG_ASSUMPTION = "assumption";
   public static final String TAG_MARKER_MESSAGE = "markerMessage";
   public static final String TAG_CALLED_METHODS = "calledMethods";
   public static final String TAG_CALLED_METHOD = "calledMethod";
   public static final String TAG_REFERENCES = "references";
   public static final String TAG_AXIOM_REFERENCE = "axiomReference";
   public static final String TAG_INVARIANT_REFERENCE = "invariantReference";
   public static final String TAG_ACCESS_REFERENCES = "accessReferences";
   public static final String TAG_ACCESS_REFERENCE = "accessReference";
   public static final String TAG_CALLMETHOD_REFERENCES = "callMethodReferences";
   public static final String TAG_CALLMETHOD_REFERENCE = "callMethodReference";
   public static final String TAG_SUBMETHOD_REFERENCE = "subMethodReference";
   public static final String TAG_INLINEMETHOD_REFERENCES = "inlineMethodReferences";
   public static final String TAG_INLINEMETHOD_REFERENCE = "inlineMethodReference";
   public static final String TAG_CONTRACT_REFERENCES = "contractReferences";
   public static final String TAG_CONTRACT_REFERENCE = "contractReference";
   
   
   
   public static final String ATTRIBUTE_MD5 = "proofFileMD5";
   public static final String ATTRIBUTE_PROOF_CLOSED = "proofClosed";
   public static final String ATTRIBUTE_PROOF_OUTDATED = "proofOutdated";
   public static final String ATTRIBUTE_NAME = "name";
   public static final String ATTRIBUTE_PROOF_FILE = "proofFile";
   public static final String ATTRIBUTE_KIND = "kind";
   public static final String ATTRIBUTE_TARGET = "target";
   public static final String ATTRIBUTE_TYPE = "type";
   public static final String ATTRIBUTE_FULL_QUALIFIED_NAME = "fullQualifiedName";
   public static final String ATTRIBUTE_KJT = "kjt";
   public static final String ATTRIBUTE_SRC = "src";
   public static final String ATTRIBUTE_PARAMETERS = "parameters";
   public static final String ATTRIBUTE_REP = "rep";
   

   /**
    * Forbid instances.
    */
   private ProofMetaFileWriter() {
   }
   
   /**
    * Creates the meta file for the given {@link ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @throws Exception
    */
   public static void writeMetaFile(ProofElement pe) throws Exception {
      final IFile metaIFile = pe.getMetaFile();
      final String encoding = "UTF-8";
      final String xml = toXml(pe, encoding);
      final byte[] bytes = xml.getBytes(encoding);
      IWorkspaceRunnable operation = new IWorkspaceRunnable() {
         @Override
         public void run(IProgressMonitor monitor) throws CoreException {
            if (!metaIFile.exists()) {
               metaIFile.create(new ByteArrayInputStream(bytes), true, null);
            }
            else {
               // Make sure that file is not read-only for compatibility with older relases. But do not set read-only flag because it requires admin rights on Mac OS to delete it.
               if (metaIFile.isReadOnly()) {
                  ResourceAttributes resAttr = metaIFile.getResourceAttributes();
                  resAttr.setReadOnly(false);
                  metaIFile.setResourceAttributes(resAttr);
               }
               metaIFile.setContents(new ByteArrayInputStream(bytes), true, true, null);
            }
         }
      };
      ResourcesPlugin.getWorkspace().run(operation, null, IWorkspace.AVOID_UPDATE, null);
   }
   
   private static String toXml(ProofElement pe, String encoding) throws Exception {
      Set<KeYJavaType> types = new LinkedHashSet<KeYJavaType>(); 
      Set<IProofReference<?>> assumptions = new LinkedHashSet<IProofReference<?>>();
      analyseDependencies(pe, types, assumptions);
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(encoding, sb);
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_MD5, ResourceUtil.computeContentMD5(pe.getProofFile()));
      attributeValues.put(ATTRIBUTE_PROOF_CLOSED, String.valueOf(pe.getProofClosed()));
      attributeValues.put(ATTRIBUTE_PROOF_OUTDATED, String.valueOf(pe.getOutdated()));
      XMLUtil.appendStartTag(0, TAG_PROOF_META_FILE, attributeValues, sb);
      appendMarkerMessage(pe, 1, sb);
      appendUsedTypes(pe, 1, types, sb);
      appendUsedContracts(pe, 1, sb);
      appendCalledMethods(pe, 1, sb);
      appendAssumptions(pe, 1, assumptions, sb);
      appendReferences(pe.getProofMetaReferences(), 1, sb);
      XMLUtil.appendEndTag(0, TAG_PROOF_META_FILE, sb);
      return sb.toString();
   }

   private static void analyseDependencies(ProofElement pe, 
                                           Set<KeYJavaType> typesToFill, 
                                           Set<IProofReference<?>> assumptionsToFill) throws ProofReferenceException {
      LinkedHashSet<IProofReference<?>> proofReferences = pe.getProofReferences();
      for (IProofReference<?> proofRef : proofReferences) {
         KeYJavaType kjt = KeYResourcesUtil.getKeYJavaType(proofRef);
         if (!KeYResourcesUtil.filterKeYJavaType(kjt)) {
            typesToFill.add(kjt);
         }
         else {
            assumptionsToFill.add(proofRef);
         }
      }
   }
   

   private static void appendMarkerMessage(ProofElement pe, int level, StringBuffer sb) {
      if (pe.getMarkerMsg() != null) {
         XMLUtil.appendStartTag(level, TAG_MARKER_MESSAGE, null, sb);
         sb.append(XMLUtil.encodeText(pe.getMarkerMsg()));
         XMLUtil.appendEndTag(level, TAG_MARKER_MESSAGE, sb);
      }
   }

   private static void appendUsedTypes(ProofElement pe, int level, Set<KeYJavaType> types, StringBuffer sb) {
      if (!types.isEmpty()) {
         XMLUtil.appendStartTag(level, TAG_USED_TYPES, null, sb);
         for (KeYJavaType kjt : types) {
            kjt = getKeYJavaTypeFromEnv(kjt, pe.getKeYEnvironment());
            Map<String, String> attributeValues = new LinkedHashMap<String, String>();
            attributeValues.put(ATTRIBUTE_NAME, kjt.getFullName());
            XMLUtil.appendStartTag(level + 1, TAG_TYPE, attributeValues, sb);
            ImmutableList<KeYJavaType> subTypes = pe.getKeYEnvironment().getServices().getJavaInfo().getAllSubtypes(kjt);
            for (KeYJavaType subType : subTypes) {
               Map<String, String> subAttributeValues = new LinkedHashMap<String, String>();
               subAttributeValues.put(ATTRIBUTE_NAME, subType.getFullName());
               XMLUtil.appendEmptyTag(level + 2, TAG_SUB_TYPE, subAttributeValues, sb);
            }
            XMLUtil.appendEndTag(level + 1, TAG_TYPE, sb);
         }
         XMLUtil.appendEndTag(level, TAG_USED_TYPES, sb);
      }
   }
   
   private static void appendUsedContracts(ProofElement pe, int level, StringBuffer sb) {
      List<IFile> usedContractsProofElements = pe.getUsedContracts();
      if (!CollectionUtil.isEmpty(usedContractsProofElements)) {
         XMLUtil.appendStartTag(level, TAG_USED_CONTRACTS, null, sb);
         for (IFile usedContractProofElement : usedContractsProofElements) {
            Map<String, String> attributeValues = new LinkedHashMap<String, String>();
            attributeValues.put(ATTRIBUTE_PROOF_FILE, usedContractProofElement.getFullPath().toString());
            XMLUtil.appendEmptyTag(level + 1, TAG_USED_CONTRACT, attributeValues, sb);
         }
         XMLUtil.appendEndTag(level, TAG_USED_CONTRACTS, sb);
      }
   }
   
   private static void appendCalledMethods(ProofElement pe, int level, StringBuffer sb) {
      List<String> calledMethods = pe.getCalledMethods();
      if (!CollectionUtil.isEmpty(calledMethods)) {
         XMLUtil.appendStartTag(level, TAG_CALLED_METHODS, null, sb);
         for (String calledMethod : calledMethods) {
            Map<String, String> attributeValues = new LinkedHashMap<String, String>();
            attributeValues.put(ATTRIBUTE_FULL_QUALIFIED_NAME, calledMethod);
            XMLUtil.appendEmptyTag(level + 1, TAG_CALLED_METHOD, attributeValues, sb);
         }
         XMLUtil.appendEndTag(level, TAG_CALLED_METHODS, sb);
      }
   }

   private static void appendAssumptions(ProofElement pe, int level, Set<IProofReference<?>> assumptions, StringBuffer sb) throws ProofReferenceException {
      if (!assumptions.isEmpty()) {
         XMLUtil.appendStartTag(level, TAG_ASSUMPTIONS, null, sb);
         for (IProofReference<?> proofRef : assumptions) {
            Object target = proofRef.getTarget();
            if(IProofReference.USE_AXIOM.equals(proofRef.getKind())){
               if(target instanceof ClassAxiom){
                  ClassAxiom classAx = (ClassAxiom) target;
                  Map<String, String> attributeValues = new LinkedHashMap<String, String>();
                  attributeValues.put(ATTRIBUTE_KIND, proofRef.getKind());
                  attributeValues.put(ATTRIBUTE_NAME, classAx.getDisplayName());
                  attributeValues.put(ATTRIBUTE_TARGET, ClassTree.getDisplayName(pe.getKeYEnvironment().getServices(), classAx.getTarget()));
                  attributeValues.put(ATTRIBUTE_TYPE, classAx.getKJT().getFullName());
                  XMLUtil.appendEmptyTag(level + 1, TAG_ASSUMPTION, attributeValues, sb);
               }
               else {
                  throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected ClassAxiom");
               }
            }
            else if(IProofReference.USE_CONTRACT.equals(proofRef.getKind())){
               if(target instanceof Contract){
                  Contract contract = (Contract) target;
                  Map<String, String> attributeValues = new LinkedHashMap<String, String>();
                  attributeValues.put(ATTRIBUTE_KIND, proofRef.getKind());
                  attributeValues.put(ATTRIBUTE_NAME, contract.getDisplayName());
                  attributeValues.put(ATTRIBUTE_TARGET, ClassTree.getDisplayName(pe.getKeYEnvironment().getServices(), contract.getTarget()));
                  attributeValues.put(ATTRIBUTE_TYPE, contract.getKJT().getFullName());
                  XMLUtil.appendEmptyTag(level + 1, TAG_ASSUMPTION, attributeValues, sb);
               }
               else {
                  throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected Contract");
               }
            }
            else if(IProofReference.USE_INVARIANT.equals(proofRef.getKind())){
               if(target instanceof ClassInvariant){
                  ClassInvariant classInv = (ClassInvariant) target;
                  Map<String, String> attributeValues = new LinkedHashMap<String, String>();
                  attributeValues.put(ATTRIBUTE_KIND, proofRef.getKind());
                  attributeValues.put(ATTRIBUTE_NAME, classInv.getDisplayName());
                  attributeValues.put(ATTRIBUTE_TYPE, classInv.getKJT().getFullName());
                  XMLUtil.appendEmptyTag(level + 1, TAG_ASSUMPTION, attributeValues, sb);
               }
               else {
                  throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected ClassInvariant");
               }
            }
         }
         XMLUtil.appendEndTag(level, TAG_ASSUMPTIONS, sb);
      }
   }
   
   
   private static void appendReferences(ProofMetaReferences references, int level, StringBuffer sb){
      String contract = references.getContract();
      ProofMetaReferenceAxiom axiom = references.getAxiom();
      ProofMetaReferenceInvariant invariant = references.getInvariant();
      List<ProofMetaReferenceAccess> accesses = references.getAccesses();
      List<ProofMetaReferenceCallMethod> callMethods = references.getCallMethods();
      List<ProofMetaReferenceMethod> inlineMethods = references.getInlineMethods();
      List<ProofMetaReferenceContract> contracts = references.getContracts();
      if(contract != null){
         Map<String, String> attributeValues = new LinkedHashMap<String, String>();
         attributeValues.put(ATTRIBUTE_REP, contract);
         XMLUtil.appendStartTag(level, TAG_REFERENCES, attributeValues, sb);
            if(axiom != null){
               attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_KJT, axiom.getKjt());
               attributeValues.put(ATTRIBUTE_NAME, axiom.getName());
               attributeValues.put(ATTRIBUTE_REP, axiom.getOriginalRep());
               XMLUtil.appendEmptyTag(level + 1, TAG_AXIOM_REFERENCE, attributeValues, sb);
            }
            if(invariant != null){
               attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_KJT, invariant.getKjt());
               attributeValues.put(ATTRIBUTE_NAME, invariant.getName());
               attributeValues.put(ATTRIBUTE_REP, invariant.getOriginalInv());
               XMLUtil.appendEmptyTag(level + 1, TAG_INVARIANT_REFERENCE, attributeValues, sb);
            }
            appendAccessReferences(accesses, level + 1, sb);
            appendCallMethodReferences(callMethods, level + 1, sb);
            appendInlineMethodReferences(inlineMethods, level + 1, sb);
            appendContractReferences(contracts, level + 1, sb);
         XMLUtil.appendEndTag(level, TAG_REFERENCES, sb);
      }
   }
   
   private static void appendAccessReferences(List<ProofMetaReferenceAccess> accesses, int level, StringBuffer sb){
      if(!accesses.isEmpty()){
         XMLUtil.appendStartTag(level, TAG_ACCESS_REFERENCES, null, sb);
         for(ProofMetaReferenceAccess access : accesses){
            if(access != null){
               Map<String, String> attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_KJT, access.getKjt());
               attributeValues.put(ATTRIBUTE_NAME, access.getName());
               attributeValues.put(ATTRIBUTE_SRC, access.getSource());
               XMLUtil.appendEmptyTag(level + 1, TAG_ACCESS_REFERENCE, attributeValues, sb);
            }
         }
         XMLUtil.appendEndTag(level, TAG_ACCESS_REFERENCES, sb);
      }
   }
   
   private static void appendCallMethodReferences(List<ProofMetaReferenceCallMethod> callMethods, int level, StringBuffer sb){
      if(!callMethods.isEmpty()){
         XMLUtil.appendStartTag(level, TAG_CALLMETHOD_REFERENCES, null, sb);
         for(ProofMetaReferenceCallMethod callMethod : callMethods){
            if(callMethod != null){
               Map<String, String> attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_KJT, callMethod.getKjt());
               attributeValues.put(ATTRIBUTE_NAME, callMethod.getName());
               attributeValues.put(ATTRIBUTE_PARAMETERS, callMethod.getParameters());
               attributeValues.put(ATTRIBUTE_SRC, callMethod.getSource());
               XMLUtil.appendStartTag(level + 1, TAG_CALLMETHOD_REFERENCE, attributeValues, sb);
               for(ProofMetaReferenceMethod subMethod : callMethod.getSubImpl()){
                  if(subMethod != null){
                     Map<String, String> subAttributeValues = new LinkedHashMap<String, String>();
                     subAttributeValues.put(ATTRIBUTE_KJT, subMethod.getKjt());
                     subAttributeValues.put(ATTRIBUTE_NAME, subMethod.getName());
                     subAttributeValues.put(ATTRIBUTE_PARAMETERS, subMethod.getParameters());
                     subAttributeValues.put(ATTRIBUTE_SRC, subMethod.getSource());
                     XMLUtil.appendEmptyTag(level + 2, TAG_SUBMETHOD_REFERENCE, subAttributeValues, sb);
                  }
               }
               XMLUtil.appendEndTag(level + 1, TAG_CALLMETHOD_REFERENCE, sb);
            }
         }
         XMLUtil.appendEndTag(level, TAG_CALLMETHOD_REFERENCES, sb);
      }
   }
   
   
   private static void appendInlineMethodReferences(List<ProofMetaReferenceMethod> inlineMethods, int level, StringBuffer sb){
      if(!inlineMethods.isEmpty()){
         XMLUtil.appendStartTag(level, TAG_INLINEMETHOD_REFERENCES, null, sb);
         for(ProofMetaReferenceMethod inlineMethod : inlineMethods){
            if(inlineMethod != null){
               Map<String, String> attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_KJT, inlineMethod.getKjt());
               attributeValues.put(ATTRIBUTE_NAME, inlineMethod.getName());
               attributeValues.put(ATTRIBUTE_PARAMETERS, inlineMethod.getParameters());
               attributeValues.put(ATTRIBUTE_SRC, inlineMethod.getSource());
               XMLUtil.appendEmptyTag(level + 1, TAG_INLINEMETHOD_REFERENCE, attributeValues, sb);
            }
         }
         XMLUtil.appendEndTag(level, TAG_INLINEMETHOD_REFERENCES, sb);
      }
   }
   
   
   private static void appendContractReferences(List<ProofMetaReferenceContract> contracts, int level, StringBuffer sb){
      if(!contracts.isEmpty()){
         XMLUtil.appendStartTag(level, TAG_CONTRACT_REFERENCES, null, sb);
         for(ProofMetaReferenceContract contract : contracts){
            if(contract != null){
               Map<String, String> attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_NAME, contract.getName());
               attributeValues.put(ATTRIBUTE_REP, contract.getContract());
               XMLUtil.appendEmptyTag(level + 1, TAG_CONTRACT_REFERENCE, attributeValues, sb);
            }
         }
         XMLUtil.appendEndTag(level, TAG_CONTRACT_REFERENCES, sb);
      }
   }
   
   
   /**
    * Returns the equivalent {@link KeYJavaType} from the given {@link KeYEnvironment} for the given {@link KeYJavaType}.
    * @param kjt - the {@link KeYJavaType} to use
    * @param environment - the {@link KeYEnvironment} to use
    * @return the {@link KeYJavaType} form the {@link KeYEnvironment}
    */
   private static KeYJavaType getKeYJavaTypeFromEnv(KeYJavaType kjt, KeYEnvironment<CustomUserInterface> environment){
      Set<KeYJavaType> envKjts = environment.getJavaInfo().getAllKeYJavaTypes();
      for(KeYJavaType envKjt : envKjts){
         if(envKjt.getFullName().equals(kjt.getFullName())){
            return envKjt;
         }
      }
      return null;
   }
}