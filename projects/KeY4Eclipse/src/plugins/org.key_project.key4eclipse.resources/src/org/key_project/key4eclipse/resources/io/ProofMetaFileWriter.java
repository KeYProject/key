package org.key_project.key4eclipse.resources.io;

import java.io.File;
import java.util.LinkedHashSet;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeY4EclipseResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
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
   
   public IFile writeMetaFile(ProofElement pe) {
      IFile metaIFile = null;
      try{
         this.environment = pe.getKeYEnvironment();
         this.addedTypes = new LinkedHashSet<KeYJavaType>();
         Document doc = createDoument(pe);
         
         TransformerFactory transFactory = TransformerFactory.newInstance();
         Transformer transformer = transFactory.newTransformer();
         DOMSource source = new DOMSource(doc);
         metaIFile = createMetaFile(pe.getProofFile());
         File metaFile = metaIFile.getLocation().toFile();
         StreamResult result = new StreamResult(metaFile);
         transformer.transform(source, result);
         metaIFile.setHidden(KeYProjectProperties.isHideMetaFiles(metaIFile.getProject()));
         metaIFile.refreshLocal(IResource.DEPTH_INFINITE, null);
      } catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
      return metaIFile;
   }
   
   
   private Document createDoument(ProofElement pe) throws ParserConfigurationException{
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
      
      Document doc = docBuilder.newDocument();
      
      Element rootElement = doc.createElement("ProofMetaFile");
      doc.appendChild(rootElement);
      
      Element proofFileHashCode = doc.createElement("proofFileHashCode");
      String hashCode = String.valueOf(pe.getProofFile().hashCode());
      proofFileHashCode.appendChild(doc.createTextNode(hashCode));
      rootElement.appendChild(proofFileHashCode);
      LinkedHashSet<IProofReference<?>> proofReferences = pe.getProofReferences();
      for(IProofReference<?> proofRef : proofReferences){
         KeYJavaType kjt = getKeYJavaType(proofRef);
         if(!KeY4EclipseResourcesUtil.filterKeYJavaType(kjt) && !addedTypes.contains(kjt)){
            addedTypes.add(kjt);
            Element typeElement = doc.createElement("type");
            typeElement.appendChild(doc.createTextNode(kjt.getFullName()));
            if(IProofReference.CALL_METHOD.equals(proofRef.getKind())){
               ImmutableList<KeYJavaType> subTypes = environment.getServices().getJavaInfo().getAllSubtypes(kjt);
               for(KeYJavaType subType : subTypes){
                  Element subTypeElement = doc.createElement("subType");
                  subTypeElement.appendChild(doc.createTextNode(subType.getFullName()));
                  typeElement.appendChild(subTypeElement);
               }
            }
            rootElement.appendChild(typeElement);
         }
      }
      return doc;
   }
   
   
   private KeYJavaType getKeYJavaType(IProofReference<?> proofRef){
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
      return kjt;
   }

   
   private IFile createMetaFile(IFile proofFile) throws CoreException{
      IPath proofFilePath = proofFile.getFullPath();
      IPath metaFilePath = proofFilePath.addFileExtension("meta");
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IFile metaFile = root.getFile(metaFilePath);
      if(!metaFile.exists()){
         metaFile.create(null, true, null);
      }
      return metaFile;
   }
}
