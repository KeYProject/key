package org.key_project.key4eclipse.resources.io;

import java.util.LinkedList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.resources.IFile;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
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
   private LinkedList<ProofMetaFileTypeElement> typeElemens;
   
   
   /**
    * The Constructor that automatically reads the given meta{@link IFile} and Provides the content.
    * @param metaIFile
    * @throws ParserConfigurationException 
    * @throws Exception
    */
   public ProofMetaFileReader(IFile metaIFile) throws Exception{ //No there are more --> Change Exception to ProofMetaFileContentException. Other exceptions are never thrown. It is legal for me to throw SAXException 
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder dBuilder = docFactory.newDocumentBuilder();
      try{
         Document doc = dBuilder.parse(metaIFile.getContents());
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
         NamedNodeMap attrMap = node.getAttributes();
         if(attrMap.getLength() == 1){
            Node attrNode = attrMap.item(0);
            if("md5".equals(attrNode.getNodeName())){
               String md5 = attrNode.getNodeValue();
               return md5;
            }
            else{
               throw new ProofMetaFileContentException("No md5 attribute found for proofFileMD5");
            }
         }
         else{
            throw new ProofMetaFileContentException("To many attributes for proofFileMD5");
         }
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
         if("type".equals(node.getNodeName()) && i != 0){
            NamedNodeMap attrMap = node.getAttributes();
            if(attrMap.getLength() == 1){
               Node attrNode = attrMap.item(0);
               if("name".equals(attrNode.getNodeName())){
                  String name = attrNode.getNodeValue();
                  typeElements.add(new ProofMetaFileTypeElement(name, readAllSubTypes(node)));
               }
               else{
                  throw new ProofMetaFileContentException("No type attribute found for this type");
               }
            }
            else{
               throw new ProofMetaFileContentException("To many attributes for this type");
            }
         }
         else if(i == 0 && !"proofFileMD5".equals(node.getNodeName())){
            throw new ProofMetaFileContentException("Illegal entry in file. First Element is not MD5");
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
         if("subType".equals(subNode.getNodeName())){
            NamedNodeMap attrMap = node.getAttributes();
            if(attrMap.getLength() == 1){
               Node attrNode = attrMap.item(0);
               if("name".equals(attrNode.getNodeName())){
                  String name = attrNode.getNodeValue();
                  subTypeList.add(name);
               }
               else{
                  throw new ProofMetaFileContentException("No type attribute found for this subtype");
               }
            }
            else{
               throw new ProofMetaFileContentException("To many attributes for this subtype");
            }
         }
         else{
            throw new ProofMetaFileContentException("Illegal entry in this file");
         }
      }
      return subTypeList;
   }
}