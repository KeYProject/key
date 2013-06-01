package org.key_project.key4eclipse.resources.meta;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashSet;

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
   
   private int proofFileHashCode;
   private LinkedHashSet<String> types;
   
   public int getProofFileHashCode(){
      return proofFileHashCode;
   }
   
   public LinkedHashSet<String> getTypes(){
      return types;
   }
   
   public void readProofMetaFile(IFile metaIFile) throws SAXException, IOException, ParserConfigurationException{
      proofFileHashCode = -1;
      types = new LinkedHashSet<String>();
      File metaFile = metaIFile.getLocation().toFile();
      DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
      DocumentBuilder dBuilder = docFactory.newDocumentBuilder();
      Document doc = dBuilder.parse(metaFile);
      Element rootElement = doc.getDocumentElement();
      NodeList nodeList = rootElement.getChildNodes();
      for(int i = 0; i < nodeList.getLength(); i++){
         Node node = nodeList.item(i);
         String nodeName = node.getNodeName();
         if(nodeName.equals("proofFileHashCode")){
            String value = node.getTextContent();
            proofFileHashCode = Integer.valueOf(value);
         }
         else if(nodeName.equals("type")){
            String value = node.getTextContent();
            types.add(value);
         }
      }
   }
}
