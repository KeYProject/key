package org.key_project.key4eclipse.resources.io;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.resources.IFile;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class ProofMetaFileReader {
   
   private Element rootElement;
   private int proofFileHashCode;
   LinkedList<ProofMetaFileTypeElement> typeElemens;
   
   
   public ProofMetaFileReader(IFile metaIFile) throws Exception{
      File metaFile = metaIFile.getLocation().toFile();
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder dBuilder = docFactory.newDocumentBuilder();
      Document doc = dBuilder.parse(metaFile);
      this.rootElement = doc.getDocumentElement();
      this.proofFileHashCode = readHashCode();
      this.typeElemens = readAllTypeElements();
   }
   
   
   
   
   public int getProofFileHashCode() {
      return proofFileHashCode;
   }




   public LinkedList<ProofMetaFileTypeElement> getTypeElements() {
      return typeElemens;
   }




   private LinkedList<ProofMetaFileTypeElement> readAllTypeElements() throws ProofMetaFileContentException{
      LinkedList<ProofMetaFileTypeElement> typeElements = new LinkedList<ProofMetaFileTypeElement>();
      NodeList nodeList = rootElement.getChildNodes();
      for(int i = 0; i < nodeList.getLength(); i++){
         Node node = nodeList.item(i);
         if(i == 0){
            if(!"proofFileHashCode".equals(node.getNodeName())){
               throw new ProofMetaFileContentException("No prooffile-hashCode found in this file");
            }
         }
         else if("type".equals(node.getNodeName())){
            typeElements.add(new ProofMetaFileTypeElement(node.getFirstChild().getTextContent(), readAllSubTypes(node)));
         }
         else{
            throw new ProofMetaFileContentException("Illegal entry in file");
         }
      }
      if(!typeElements.isEmpty()){
         return typeElements;
      }
      else{
         throw new ProofMetaFileContentException("No types found in this file");
      }
         
   }
   
   
   private int readHashCode() throws ProofMetaFileContentException{
      NodeList nodeList = rootElement.getElementsByTagName("proofFileHashCode");
      if(nodeList.getLength() == 1){
         Node node = nodeList.item(0);
         String textContext = node.getTextContent();
         Integer hashCode = Integer.valueOf(textContext);
         return hashCode;
      }
      else if(nodeList.getLength() > 1){
         throw new ProofMetaFileContentException("More then one prooffile-hashcode found in this file");
      }
      else{
         throw new ProofMetaFileContentException("No prooffile-hashCode found in this file");
      }
   }
   
   
   private LinkedList<String> readAllSubTypes(Node node) throws ProofMetaFileContentException{
      LinkedList<String> subTypeList = new LinkedList<String>();
      NodeList nodeList = node.getChildNodes();
      for(int i = 0; i < nodeList.getLength(); i++){
         Node subNode = nodeList.item(i);
         if(i == 0){
            if(!"#text".equals(subNode.getNodeName())){
               throw new ProofMetaFileContentException("Illegal entry in this file");
            }
         }
         else if("subType".equals(subNode.getNodeName())){
            subTypeList.add(subNode.getTextContent());
         }
         else{
            throw new ProofMetaFileContentException("Illegal entry in this file");
         }
      }
      return subTypeList;
   }
}
