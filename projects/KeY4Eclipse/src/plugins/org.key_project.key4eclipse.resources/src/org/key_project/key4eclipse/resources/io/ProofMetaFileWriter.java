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
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourceAttributes;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.XMLUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
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
   public static final String ATTRIBUTE_MD5 = "proofFileMD5";
   public static final String ATTRIBUTE_PROOF_CLOSED = "proofClosed";
   public static final String ATTRIBUTE_NAME = "name";
   public static final String ATTRIBUTE_PROOF_FILE = "proofFile";
   public static final String ATTRIBUTE_KIND = "kind";
   public static final String ATTRIBUTE_TARGET = "target";
   public static final String ATTRIBUTE_TYPE = "type";

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
      IFile metaIFile = pe.getMetaFile();
      String encoding = "UTF-8";
      String xml = toXml(pe, encoding);
      if (!metaIFile.exists()) {
         metaIFile.create(new ByteArrayInputStream(xml.getBytes(encoding)), true, null);
      }
      else {
         ResourceAttributes resAttr = metaIFile.getResourceAttributes();
         resAttr.setReadOnly(false);
         metaIFile.setResourceAttributes(resAttr);
         metaIFile.setContents(new ByteArrayInputStream(xml.getBytes(encoding)), true, true, null);
      }
      metaIFile.setHidden(KeYProjectProperties.isHideMetaFiles(metaIFile.getProject()));
      ResourceAttributes resAttr = metaIFile.getResourceAttributes();
      resAttr.setReadOnly(true);
      metaIFile.setResourceAttributes(resAttr);
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
      XMLUtil.appendStartTag(0, TAG_PROOF_META_FILE, attributeValues, sb);
      appendMarkerMessage(pe, 1, sb);
      appendUsedTypes(pe, 1, types, sb);
      appendUsedContracts(pe, 1, sb);
      appendAssumptions(pe, 1, assumptions, sb);
      XMLUtil.appendEndTag(0, TAG_PROOF_META_FILE, sb);
      return sb.toString();
   }

   private static void analyseDependencies(ProofElement pe, 
                                           Set<KeYJavaType> typesToFill, 
                                           Set<IProofReference<?>> assumptionsToFill) throws ProofReferenceException {
      LinkedHashSet<IProofReference<?>> proofReferences = pe.getProofReferences();
      for (IProofReference<?> proofRef : proofReferences) {
         KeYJavaType kjt = getKeYJavaType(proofRef);
         if (!KeYResourcesUtil.filterKeYJavaType(kjt)) {
            typesToFill.add(kjt);
         }
         else {
            assumptionsToFill.add(proofRef);
         }
      }
   }
   
   /**
    * Returns the {@link KeYJavaType} for the given {@link IProofReference}.
    * @param proofRef - the {@link IProofReference} to use
    * @return the {@link KeYJavaType}
    * @throws ProofReferenceException 
    */
   private static KeYJavaType getKeYJavaType(IProofReference<?> proofRef) throws ProofReferenceException{
      KeYJavaType kjt = null;
      Object target = proofRef.getTarget();
      if(IProofReference.ACCESS.equals(proofRef.getKind())){
         if(target instanceof IProgramVariable){
            IProgramVariable progVar = (IProgramVariable) target;
            kjt = progVar.getKeYJavaType();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramVariable");
         }
      }
      else if(IProofReference.CALL_METHOD.equals(proofRef.getKind()) || 
              IProofReference.INLINE_METHOD.equals(proofRef.getKind())){
         if(target instanceof IProgramMethod){
            IProgramMethod progMeth = (IProgramMethod) target;
            kjt = progMeth.getContainerType();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramMethod");
         }
      }
      else if(IProofReference.USE_AXIOM.equals(proofRef.getKind())){
         if(target instanceof ClassAxiom){
            ClassAxiom classAx = (ClassAxiom) target;
            kjt = classAx.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected ClassAxiom");
         }
      }
      else if(IProofReference.USE_CONTRACT.equals(proofRef.getKind())){
         if(target instanceof Contract){
            Contract contract = (Contract) target;
            kjt = contract.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected Contract");
         }
      }
      else if(IProofReference.USE_INVARIANT.equals(proofRef.getKind())){
         if(target instanceof ClassInvariant){
            ClassInvariant classInv = (ClassInvariant) target;
            kjt = classInv.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected ClassInvariant");
         }
      }
      else {
         throw new ProofReferenceException("Unknow proof reference kind found: " + proofRef.getKind());
      }
      return kjt;
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
      LinkedList<ProofElement> usedContractsProofElements = pe.getUsedContracts();
      if (!usedContractsProofElements.isEmpty()) {
         XMLUtil.appendStartTag(level, TAG_USED_CONTRACTS, null, sb);
         for (ProofElement usedContractProofElement : usedContractsProofElements) {
            Map<String, String> attributeValues = new LinkedHashMap<String, String>();
            attributeValues.put(ATTRIBUTE_PROOF_FILE, usedContractProofElement.getProofFile().getFullPath().toString());
            XMLUtil.appendEmptyTag(level + 1, TAG_USED_CONTRACT, attributeValues, sb);
         }
         XMLUtil.appendEndTag(level, TAG_USED_CONTRACTS, sb);
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