package org.key_project.key4eclipse.resources.io;

import java.io.File;
import java.util.LinkedList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.eclipse.core.resources.IFile;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * Reader for the meta files.
 * @author Stefan Käsdorf
 */
public class ProofMetaFileReader {
   
   private Element rootElement;
   private String proofFileMD5;
   LinkedList<ProofMetaFileTypeElement> typeElemens; // TODO: Make private
   
   
   /**
    * The Constructor that automatically reads the given meta{@link IFile} and Provides the content.
    * @param metaIFile
    * @throws Exception
    */
   public ProofMetaFileReader(IFile metaIFile) throws Exception{ // Change Exception to ProofMetaFileContentException. Other exceptions are never thrown. It is legal for me to throw SAXException 
      File metaFile = metaIFile.getLocation().toFile();
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder dBuilder = docFactory.newDocumentBuilder();
      try{
         Document doc = dBuilder.parse(metaFile); // TODO: Use metaIFIle.getContents() instead
         this.rootElement = doc.getDocumentElement();
         this.proofFileMD5 = readMD5();
         this.typeElemens = readAllTypeElements();
      } catch (SAXException e){
         throw new ProofMetaFileContentException("Invalid XML File");
      }
   }
   
   
   /**
    * Returns the read MD5 Sum.
    * @return - the MD5 Sum
    */
   public String getProofFileMD5() {
      return proofFileMD5;
   }


   /**
    * Return the {@link LinkedList} with all {@link ProofMetaFileTypeElement}s.
    * @return the {@link ProofMetaFileTypeElement}s
    */
   public LinkedList<ProofMetaFileTypeElement> getTypeElements() {
      return typeElemens;
   }


   /**
    * Reads the MD5 Sum form the metaFile.
    * @return - the MD5 Sum
    * @throws ProofMetaFileContentException
    */
   private String readMD5() throws ProofMetaFileContentException{
      NodeList nodeList = rootElement.getElementsByTagName("proofFileMD5");
      if(nodeList.getLength() == 1){
         Node node = nodeList.item(0);
         return node.getTextContent();
      }
      else if(nodeList.getLength() > 1){
         throw new ProofMetaFileContentException("More then one prooffile-MD5 found in this file");
      }
      else{
         throw new ProofMetaFileContentException("No prooffile-MD5 found in this file");
      }
   }
   
   
   /**
    * Reads all types stored in the meta file.
    * @return a {@link LinkedList} with all read types
    * @throws ProofMetaFileContentException
    */
   private LinkedList<ProofMetaFileTypeElement> readAllTypeElements() throws ProofMetaFileContentException{
      LinkedList<ProofMetaFileTypeElement> typeElements = new LinkedList<ProofMetaFileTypeElement>();
      NodeList nodeList = rootElement.getChildNodes();
      for(int i = 0; i < nodeList.getLength(); i++){
         Node node = nodeList.item(i);
         if(i == 0){
            if(!"proofFileMD5".equals(node.getNodeName())){
               throw new ProofMetaFileContentException("No prooffile-MD5 found in this file");
            }
         }
         else if("type".equals(node.getNodeName())){
            typeElements.add(new ProofMetaFileTypeElement(node.getFirstChild().getTextContent(), readAllSubTypes(node)));
         }
         else{
            throw new ProofMetaFileContentException("Illegal entry in file");
         }
      }
      return typeElements;
   }
   
   
   /**
    * Reads all subTypes for the given {@link Node}.
    * @param node - the {@link Node} to use
    * @return - a {@link LinkedList} with all subTypes
    * @throws ProofMetaFileContentException
    */
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