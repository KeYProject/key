package org.key_project.key4eclipse.resources.io;

import java.io.File;
import java.util.LinkedHashSet;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
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
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Writer for the meta files.
 * @author Stefan Käsdorf
 */
public class ProofMetaFileWriter {
   
   /**
    * {@link LinkedHashSet} with the full names of all types already added to the meta file.
    */
   private LinkedHashSet<String> addedTypes;
   private ProofElement pe;
   private Document doc;
   
   
   public ProofMetaFileWriter(ProofElement pe){
      this.pe = pe;
   }
   
   /**
    * Creates the meta file for the given {@link ProofElement}.
    * @param pe - the {@link ProofElement} to use
    */
   public void writeMetaFile() {
      IFile metaIFile = pe.getMetaFile();
      try{
         this.addedTypes = new LinkedHashSet<String>();
         doc = createDoument();
         
         TransformerFactory transFactory = TransformerFactory.newInstance();
         Transformer transformer = transFactory.newTransformer();
         DOMSource source = new DOMSource(doc);
         if(!metaIFile.exists()){
            metaIFile.create(null, true, null);
         }
         File metaFile = metaIFile.getLocation().toFile();
         StreamResult result = new StreamResult(metaFile);
         transformer.transform(source, result);
         metaIFile.setHidden(KeYProjectProperties.isHideMetaFiles(metaIFile.getProject()));
         metaIFile.refreshLocal(IResource.DEPTH_INFINITE, null);
         // TODO: Make meta file read-only so that the user sees that he should not modify it.
      } catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e); // TODO: The caller should be responsible to handle exceptions. Do not catch them here
      }
   }
   
   
   /**
    * Creates the {@link Document} for the meta file of the given {@link ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @return the created {@link Document}
    * @throws ParserConfigurationException
    * @throws ProofReferenceException 
    */
   private Document createDoument() throws ParserConfigurationException, ProofReferenceException{
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
      
      doc = docBuilder.newDocument();
      
      Element rootElement = doc.createElement("ProofMetaFile");
      doc.appendChild(rootElement);
      
      Element proofFileMD5 = doc.createElement("proofFileMD5");
      String md5 = KeY4EclipseResourcesUtil.computeContentMD5(pe.getProofFile());
      proofFileMD5.appendChild(doc.createTextNode(md5));
      rootElement.appendChild(proofFileMD5);
      createTypeElement(getKeYJavaTypeFromEnv(pe.getContract().getKJT(), pe.getKeYEnvironment()));
      LinkedHashSet<IProofReference<?>> proofReferences = pe.getProofReferences();
      for(IProofReference<?> proofRef : proofReferences){
         KeYJavaType kjt = getKeYJavaType(proofRef);
         if(!KeY4EclipseResourcesUtil.filterKeYJavaType(kjt) && !addedTypes.contains(kjt.getFullName())){
            createTypeElement(getKeYJavaTypeFromEnv(kjt, pe.getKeYEnvironment()));
         }
      }
      return doc;
   }
   
   
   private void createTypeElement(KeYJavaType kjt){
      addedTypes.add(kjt.getFullName());
      Element typeElement = doc.createElement("type");
      typeElement.appendChild(doc.createTextNode(kjt.getFullName()));
      ImmutableList<KeYJavaType> subTypes = pe.getKeYEnvironment().getServices().getJavaInfo().getAllSubtypes(kjt);
      for(KeYJavaType subType : subTypes){
         Element subTypeElement = doc.createElement("subType");
         subTypeElement.appendChild(doc.createTextNode(subType.getFullName()));
         typeElement.appendChild(subTypeElement);
      }
      doc.getDocumentElement().appendChild(typeElement);
   }
   
   
   /**
    * Returns the equivalent {@link KeYJavaType} from the given {@link KeYEnvironment} for the given {@link KeYJavaType}.
    * @param kjt - the {@link KeYJavaType} to use
    * @param environment - the {@link KeYEnvironment} to use
    * @return the {@link KeYJavaType} form the {@link KeYEnvironment}
    */
   private KeYJavaType getKeYJavaTypeFromEnv(KeYJavaType kjt, KeYEnvironment<CustomConsoleUserInterface> environment){
      Set<KeYJavaType> envKjts = environment.getJavaInfo().getAllKeYJavaTypes();
      for(KeYJavaType envKjt : envKjts){
         if(envKjt.getFullName().equals(kjt.getFullName())){
            return envKjt;
         }
      }
      return null;
   }
   
   
   /**
    * Returns the {@link KeYJavaType} for the given {@link IProofReference}.
    * @param proofRef - the {@link IProofReference} to use
    * @return the {@link KeYJavaType}
    * @throws ProofReferenceException 
    */
   private KeYJavaType getKeYJavaType(IProofReference<?> proofRef) throws ProofReferenceException{
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
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramVariable");
         }
      }
      else if(IProofReference.USE_AXIOM.equals(proofRef.getKind())){
         if(target instanceof ClassAxiom){
            ClassAxiom classAx = (ClassAxiom) target;
            kjt = classAx.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramVariable");
         }
      }
      else if(IProofReference.USE_CONTRACT.equals(proofRef.getKind())){
         if(target instanceof Contract){
            Contract contract = (Contract) target;
            kjt = contract.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramVariable");
         }
      }
      else if(IProofReference.USE_INVARIANT.equals(proofRef.getKind())){
         if(target instanceof ClassInvariant){
            ClassInvariant classInv = (ClassInvariant) target;
            kjt = classInv.getKJT();
         }
         else {
            throw new ProofReferenceException("Wrong target type " + target.getClass() + " found. Expected IProgramVariable");
         }
      }
      else {
         throw new ProofReferenceException("Unknow proof reference kind found: " + proofRef.getKind());
      }
      return kjt;
   }
}