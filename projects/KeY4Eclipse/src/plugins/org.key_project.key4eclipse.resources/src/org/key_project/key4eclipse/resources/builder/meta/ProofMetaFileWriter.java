package org.key_project.key4eclipse.resources.builder.meta;

import java.io.File;
import java.util.LinkedHashSet;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.key_project.key4eclipse.resources.util.KeY4EclipseResourcesUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

public class ProofMetaFileWriter {
   private LinkedHashSet<KeYJavaType> addedTypes;
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   public IFile writeMetaFile(IFile proofFile, Proof proof, KeYEnvironment<CustomConsoleUserInterface> env) throws ParserConfigurationException, TransformerException, CoreException{
      this.environment = env;
      this.addedTypes = new LinkedHashSet<KeYJavaType>();
//      Document doc = createDoument(proofFile, proof);
      Document doc = createDocumentSimple(proofFile, proof);
      
      TransformerFactory transFactory = TransformerFactory.newInstance();
      Transformer transformer = transFactory.newTransformer();
      DOMSource source = new DOMSource(doc);
      IFile metaIFile = createMetaFile(proofFile);
      File metaFile = metaIFile.getLocation().toFile();
      StreamResult result = new StreamResult(metaFile);
      transformer.transform(source, result);
      metaIFile.refreshLocal(IResource.DEPTH_INFINITE, null);
      metaIFile.setHidden(true);
      return metaIFile;
   }
   
   
   private Document createDoument(IFile proofFile, Proof proof) throws ParserConfigurationException{
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
      
      Document doc = docBuilder.newDocument();
      
      Element rootElement = doc.createElement("ProofMetaFile");
      doc.appendChild(rootElement);
      
      Element proofFileHashCode = doc.createElement("proofFileHashCode");
      String hashCode = String.valueOf(proofFile.hashCode());
      proofFileHashCode.appendChild(doc.createTextNode(hashCode));
      rootElement.appendChild(proofFileHashCode);
      
      KeYJavaType[] kjts = collectTypesForProof(proof);
      int id = 0;
      for(KeYJavaType kjt : kjts){
         if(!addedTypes.contains(kjt)){
            addedTypes.add(kjt);
            Element type = doc.createElement("type");
            type.setAttribute("ID", id+"");
            type.appendChild(doc.createTextNode(kjt.getFullName()));
            id++;
            
            type = addSubTypes(doc, type, kjt, 1);
            
            rootElement.appendChild(type);
         }
      }
      return doc;
   }
   
   
   private Document createDocumentSimple(IFile proofFile, Proof proof) throws ParserConfigurationException{
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
      
      Document doc = docBuilder.newDocument();
      
      Element rootElement = doc.createElement("ProofMetaFile");
      doc.appendChild(rootElement);
      
      Element proofFileHashCode = doc.createElement("proofFileHashCode");
      String hashCode = String.valueOf(proofFile.hashCode());
      proofFileHashCode.appendChild(doc.createTextNode(hashCode));
      rootElement.appendChild(proofFileHashCode);
      
      KeYJavaType[] kjts = collectTypesForProof(proof);
      int id = 0;
      for(KeYJavaType kjt : kjts){
         if(!addedTypes.contains(kjt)){
            addedTypes.add(kjt);
            Element element = doc.createElement("type");
            element.setAttribute("id", id+"");
            element.appendChild(doc.createTextNode(kjt.getFullName()));
            id++;
            rootElement.appendChild(element);
         }
      }
      return doc;
   }

   
   public IFile createMetaFile(IFile proofFile) throws CoreException{
      IPath proofFilePath = proofFile.getFullPath();
      IPath metaFilePath = proofFilePath.addFileExtension("meta");
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile metaFile = root.getFile(metaFilePath);
      if(!metaFile.exists()){
         metaFile.create(null, true, null);
      }
      return metaFile;
   }
   
   
   private Element addSubTypes(Document doc, Element element, KeYJavaType kjt, int subCount){
      ImmutableList<KeYJavaType> subTypes = environment.getServices().getJavaInfo().getAllSubtypes(kjt);
      int subId = 0;
      for(KeYJavaType subType : subTypes){
         if(!addedTypes.contains(subType)){
            addedTypes.add(subType);
            String subString = computeSubString(subCount);
            Element subElement = doc.createElement(subString + "Type");
            subElement.appendChild(doc.createTextNode(subType.getFullName()));
            subElement.setAttribute(subString + "Id", subId+"");
            subId++;
            
            subElement = addSubTypes(doc, subElement, subType, subCount+1);
            
            element.appendChild(subElement);
         }
      }
      return element;
   }
   
   
   private String computeSubString(int subCount){
      String str = "";
      for(int i = 0; i < subCount; i++){
         if(i == 0){
            str = str + "sub";
         }
         else{
            str = str + "Sub";
         }
      }
      return str;
   }
   
   
   private KeYJavaType[] collectTypesForProof(Proof proof){
      Set<KeYJavaType> kjts = new LinkedHashSet<KeYJavaType>();
      LinkedHashSet<IProofReference<?>> proofRefs = ProofReferenceUtil.computeProofReferences(proof);
      for(IProofReference<?> proofRef : proofRefs){
         KeYJavaType kjt = null;
         Object target = proofRef.getTarget();
         if(target instanceof IProgramMethod){
            IProgramMethod progMeth = (IProgramMethod) target;
            kjt = progMeth.getContainerType();
         }
         else if(target instanceof IProgramVariable){
            IProgramVariable progVar = (IProgramVariable) target;
            kjt = progVar.getKeYJavaType();
         }
         else if(target instanceof Contract){
            Contract contract = (Contract) target;
            kjt = contract.getKJT();
         }
         else if(target instanceof ClassInvariant){
            ClassInvariant classInv = (ClassInvariant) target;
            kjt = classInv.getKJT();
         }
         else if(target instanceof ClassAxiom){
            ClassAxiom classAx = (ClassAxiom) target;
            kjt = classAx.getKJT();
         }
         if(kjt != null){
            if(!kjts.contains(kjt)){
               kjts.add(kjt);
            }
//            if(proofRef.getKind().equals(IProofReference.CALL_METHOD)){
//               ImmutableList<KeYJavaType> subTypes = environment.getServices().getJavaInfo().getAllSubtypes(kjt);
//               for(KeYJavaType subType : subTypes){
//                  if(!kjts.contains(subType)){
//                     kjts.add(subType);
//                  }
//               }
//            }
         }
         
      }
      
      return KeY4EclipseResourcesUtil.sortKeYJavaTypes(kjts);
   }
}
