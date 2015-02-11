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

import java.io.InputStream;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.Path;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * Reader for the meta files.
 * @author Stefan Käsdorf
 */
public class ProofMetaFileReader {
   private String proofFileMD5;
   private boolean proofClosed;
   private boolean proofOutdated;
   private String markerMessage;
   private final LinkedList<ProofMetaFileTypeElement> typeElemens = new LinkedList<ProofMetaFileTypeElement>();
   private final LinkedList<IFile> usedContracts = new LinkedList<IFile>();
   private final List<ProofMetaFileAssumption> assumptions = new LinkedList<ProofMetaFileAssumption>();
   private final List<String> calledMethods = new LinkedList<String>();

   /**
    * The Constructor that automatically reads the given meta{@link IFile} and Provides the content.
    * @param metaIFile
    * @throws ParserConfigurationException 
    * @throws Exception
    */
   public ProofMetaFileReader(IFile metaIFile) throws Exception {
      InputStream in = metaIFile.getContents();
      try {
         SAXParserFactory factory = SAXParserFactory.newInstance();
         factory.setNamespaceAware(true);
         SAXParser saxParser = factory.newSAXParser();
         MetaFileSAXHandler handler = new MetaFileSAXHandler();
         saxParser.parse(in, handler);
      }
      finally {
         in.close();
      }
   }
   
   /**
    * Utility class used by {@link ProofMetaFileReader#ProofMetaFileReader(IFile)}.
    * @author Martin Hentschel
    */
   private class MetaFileSAXHandler extends DefaultHandler {      
      /**
       * The parent hierarchy filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private final Deque<Object> parentStack = new LinkedList<Object>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         if (ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(qName)) {
            Assert.isTrue(parentStack.isEmpty());
            proofFileMD5 = getMD5(attributes);
            proofClosed = isProofClosed(attributes);
            proofOutdated = isProofOutdated(attributes);
            parentStack.addFirst(ProofMetaFileWriter.TAG_PROOF_META_FILE);
         }
         else if (ProofMetaFileWriter.TAG_MARKER_MESSAGE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_MARKER_MESSAGE  + " has to be a child of " + ProofMetaFileWriter.TAG_PROOF_META_FILE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_MARKER_MESSAGE);
         }
         else if (ProofMetaFileWriter.TAG_USED_TYPES.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_USED_TYPES  + " has to be a child of " + ProofMetaFileWriter.TAG_PROOF_META_FILE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_USED_TYPES);
         }
         else if (ProofMetaFileWriter.TAG_TYPE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_USED_TYPES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_TYPE  + " has to be a child of " + ProofMetaFileWriter.TAG_USED_TYPES + ".");
            }
            ProofMetaFileTypeElement element = new ProofMetaFileTypeElement(getName(attributes));
            typeElemens.add(element);
            parentStack.addFirst(element);
         }
         else if (ProofMetaFileWriter.TAG_SUB_TYPE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!(parent instanceof ProofMetaFileTypeElement)) {
               throw new SAXException(ProofMetaFileWriter.TAG_SUB_TYPE  + " has to be a child of " + ProofMetaFileWriter.TAG_TYPE + ".");
            }
            ((ProofMetaFileTypeElement) parent).addSubType(getName(attributes));
            parentStack.addFirst(ProofMetaFileWriter.TAG_SUB_TYPE);
         }
         else if (ProofMetaFileWriter.TAG_USED_CONTRACTS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_USED_CONTRACTS  + " has to be a child of " + ProofMetaFileWriter.TAG_PROOF_META_FILE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_USED_CONTRACTS);
         }
         else if (ProofMetaFileWriter.TAG_USED_CONTRACT.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_USED_CONTRACTS.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_USED_CONTRACT  + " has to be a child of " + ProofMetaFileWriter.TAG_USED_CONTRACTS + ".");
            }
            usedContracts.add(getProofFile(attributes));
            parentStack.addFirst(ProofMetaFileWriter.TAG_USED_CONTRACT);
         }
         else if (ProofMetaFileWriter.TAG_ASSUMPTIONS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_ASSUMPTIONS  + " has to be a child of " + ProofMetaFileWriter.TAG_PROOF_META_FILE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_ASSUMPTIONS);
         }
         else if (ProofMetaFileWriter.TAG_ASSUMPTION.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_ASSUMPTIONS.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_ASSUMPTION  + " has to be a child of " + ProofMetaFileWriter.TAG_ASSUMPTIONS + ".");
            }
            assumptions.add(new ProofMetaFileAssumption(getKind(attributes), getName(attributes), getTarget(attributes), getType(attributes)));
            parentStack.addFirst(ProofMetaFileWriter.TAG_ASSUMPTION);
         }
         else if (ProofMetaFileWriter.TAG_CALLED_METHODS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_CALLED_METHODS  + " has to be a child of " + ProofMetaFileWriter.TAG_PROOF_META_FILE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_CALLED_METHODS);
         }
         else if (ProofMetaFileWriter.TAG_CALLED_METHOD.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_CALLED_METHODS.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_CALLED_METHOD  + " has to be a child of " + ProofMetaFileWriter.TAG_CALLED_METHODS + ".");
            }
            calledMethods.add(getFullQualifiedName(attributes));
            parentStack.addFirst(ProofMetaFileWriter.TAG_CALLED_METHOD);
         }
         else {
            throw new SAXException("Unsupported element " + qName + ".");
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void characters(char[] ch, int start, int length) throws SAXException {
         Object parent = parentStack.peekFirst();
         if (ProofMetaFileWriter.TAG_MARKER_MESSAGE.equals(parent)) {
            if (markerMessage != null) {
               markerMessage += new String(ch, start, length);
            }
            else {
               markerMessage = new String(ch, start, length);
            }
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (!parentStack.isEmpty()) {
            parentStack.removeFirst();
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void endDocument() throws SAXException {
         if (markerMessage != null) {
            markerMessage = markerMessage.trim();
         }
      }

      /**
       * Returns the proof closed state.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected boolean isProofClosed(Attributes attributes) {
         String value = attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_PROOF_CLOSED);
         return value != null && Boolean.parseBoolean(value);
      }
      
      /**
       * Returns the proof outdated state.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected boolean isProofOutdated(Attributes attributes) {
         String value = attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_PROOF_OUTDATED);
         return value != null && Boolean.parseBoolean(value);
      }

      /**
       * Returns the name.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getName(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_NAME);
      }

      /**
       * Returns the kind.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getKind(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_KIND);
      }

      /**
       * Returns the target.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getTarget(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_TARGET);
      }

      /**
       * Returns the type.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getType(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_TYPE);
      }

      /**
       * Returns the ful qualified name value.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getFullQualifiedName(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_FULL_QUALIFIED_NAME);
      }
      
      /**
       * Returns the MD5 value.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getMD5(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_MD5);
      }
      
      /**
       * Returns the proof file value.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected IFile getProofFile(Attributes attributes) {
         String path = attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_PROOF_FILE);
         if (path != null) {
            return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
         }
         return null;
      }
   }

   /**
    * Returns the read MD5 Sum.
    * @return - the MD5 Sum
    */
   public String getProofFileMD5() {
      return proofFileMD5;
   }


   public boolean getProofClosed(){
      return proofClosed;
   }
   
   public boolean getProofOutdated(){
      return proofOutdated;
   }
   
   public String getMarkerMessage(){
      return markerMessage;
   }

   /**
    * Return the {@link LinkedList} with all {@link ProofMetaFileTypeElement}s.
    * @return the {@link ProofMetaFileTypeElement}s
    */
   public List<ProofMetaFileTypeElement> getTypeElements() {
      return typeElemens;
   }
   
   public LinkedList<IFile> getUsedContracts(){
      return usedContracts;
   }
   
   public List<ProofMetaFileAssumption> getAssumptions() {
      return assumptions;
   }

   public List<String> getCalledMethods() {
      return calledMethods;
   }
}