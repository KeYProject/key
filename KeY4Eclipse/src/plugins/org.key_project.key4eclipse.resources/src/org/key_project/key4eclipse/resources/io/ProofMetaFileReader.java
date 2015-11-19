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
import org.key_project.key4eclipse.resources.counterexamples.KeYProjectCounterExample;
import org.key_project.key4eclipse.resources.counterexamples.TreeElement;
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
   private final LinkedList<IFile> usedContracts = new LinkedList<IFile>();
   private final List<ProofMetaFileAssumption> assumptions = new LinkedList<ProofMetaFileAssumption>();
   private final ProofMetaReferences references = new ProofMetaReferences();
   private final List<String> calledMethods = new LinkedList<String>();
   private final List<KeYProjectCounterExample> counterExamples = new LinkedList<KeYProjectCounterExample>();

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
         else if (ProofMetaFileWriter.TAG_REFERENCES.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_REFERENCES  + " has to be a child of " + ProofMetaFileWriter.TAG_PROOF_META_FILE + ".");
            }
            references.setContract(getRep(attributes));
            parentStack.addFirst(ProofMetaFileWriter.TAG_REFERENCES);
         }
         else if(ProofMetaFileWriter.TAG_TYPE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_TYPE  + " has to be a child of " + ProofMetaFileWriter.TAG_REFERENCES + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_TYPE);
         }
         else if (ProofMetaFileWriter.TAG_AXIOM_REFERENCES.equals(qName)){
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_TYPE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_AXIOM_REFERENCES  + " has to be a child of " + ProofMetaFileWriter.TAG_TYPE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_AXIOM_REFERENCES);
         }
         else if (ProofMetaFileWriter.TAG_AXIOM_REFERENCE.equals(qName)){
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_AXIOM_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_AXIOM_REFERENCE  + " has to be a child of " + ProofMetaFileWriter.TAG_AXIOM_REFERENCES + ".");
            }
            String kjt = getKJT(attributes);
            ProofMetaReferenceAxiom axiom = new ProofMetaReferenceAxiom(kjt, getName(attributes), getRep(attributes));
            references.getPerTypeReferences(kjt).addAxiom(axiom);
            parentStack.addFirst(ProofMetaFileWriter.TAG_AXIOM_REFERENCE);
         }
         else if (ProofMetaFileWriter.TAG_INVARIANT_REFERENCES.equals(qName)){
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_TYPE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_INVARIANT_REFERENCES  + " has to be a child of " + ProofMetaFileWriter.TAG_TYPE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_INVARIANT_REFERENCES);
         }
         else if (ProofMetaFileWriter.TAG_INVARIANT_REFERENCE.equals(qName)){
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_INVARIANT_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_INVARIANT_REFERENCE  + " has to be a child of " + ProofMetaFileWriter.TAG_INVARIANT_REFERENCES + ".");
            }
            String kjt = getKJT(attributes);
            ProofMetaReferenceInvariant invariant = new ProofMetaReferenceInvariant(kjt, getName(attributes), getRep(attributes));
            references.getPerTypeReferences(kjt).addInvariant(invariant);
            parentStack.addFirst(ProofMetaFileWriter.TAG_INVARIANT_REFERENCE);
         }
         else if (ProofMetaFileWriter.TAG_ACCESS_REFERENCES.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_TYPE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_ACCESS_REFERENCES  + " has to be a child of " + ProofMetaFileWriter.TAG_TYPE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_ACCESS_REFERENCES);
         }
         else if (ProofMetaFileWriter.TAG_ACCESS_REFERENCE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_ACCESS_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_ACCESS_REFERENCE  + " has to be a child of " + ProofMetaFileWriter.TAG_ACCESS_REFERENCES + ".");
            }
            String kjt = getKJT(attributes);
            ProofMetaReferenceAccess access = new ProofMetaReferenceAccess(kjt, getName(attributes), getType(attributes), getVisibility(attributes), getIsStatic(attributes), getIsFinal(attributes), getInitializer(attributes));
            references.getPerTypeReferences(kjt).addAccess(access);
            parentStack.addFirst(ProofMetaFileWriter.TAG_ACCESS_REFERENCE);
         }
         else if (ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCES.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCES  + " has to be a child of " + ProofMetaFileWriter.TAG_REFERENCES + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCES);
         }
         else if (ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCE  + " has to be a child of " + ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCES + ".");
            }
            String kjt = getKJT(attributes);
            ProofMetaReferenceCallMethod callMethod = new ProofMetaReferenceCallMethod(kjt, getName(attributes), getParameters(attributes), getImplementations(attributes));
            references.addCallMethod(callMethod);
            parentStack.addFirst(ProofMetaFileWriter.TAG_CALLMETHOD_REFERENCE);
         }
         else if (ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCES.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_TYPE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCES  + " has to be a child of " + ProofMetaFileWriter.TAG_TYPE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCES);
         }
         else if (ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCE  + " has to be a child of " + ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCES + ".");
            }
            String kjt = getKJT(attributes);
            ProofMetaReferenceMethod inlineMethod = new ProofMetaReferenceMethod(kjt, getName(attributes), getParameters(attributes), getSrc(attributes));
            references.getPerTypeReferences(kjt).addInlineMethod(inlineMethod);
            parentStack.addFirst(ProofMetaFileWriter.TAG_INLINEMETHOD_REFERENCE);
         }
         else if (ProofMetaFileWriter.TAG_CONTRACT_REFERENCES.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_TYPE.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_CONTRACT_REFERENCES  + " has to be a child of " + ProofMetaFileWriter.TAG_TYPE + ".");
            }
            parentStack.addFirst(ProofMetaFileWriter.TAG_CONTRACT_REFERENCES);
         }
         else if (ProofMetaFileWriter.TAG_CONTRACT_REFERENCE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!ProofMetaFileWriter.TAG_CONTRACT_REFERENCES.equals(parent)) {
               throw new SAXException(ProofMetaFileWriter.TAG_CONTRACT_REFERENCE  + " has to be a child of " + ProofMetaFileWriter.TAG_CONTRACT_REFERENCES + ".");
            }
            String kjt = getKJT(attributes);
            ProofMetaReferenceContract contract = new ProofMetaReferenceContract(kjt, getName(attributes), getRep(attributes));
            references.getPerTypeReferences(kjt).addContract(contract);
            parentStack.addFirst(ProofMetaFileWriter.TAG_CONTRACT_REFERENCE);
         }
         else if(ProofMetaFileWriter.TAG_COUNTER_EXAMPLES.equals(qName)){
             Object parent = parentStack.peekFirst();
             if (!ProofMetaFileWriter.TAG_PROOF_META_FILE.equals(parent)) {
                 throw new SAXException(ProofMetaFileWriter.TAG_COUNTER_EXAMPLES  + " has to be a child of " + ProofMetaFileWriter.TAG_PROOF_META_FILE + ".");
              }
              parentStack.addFirst(ProofMetaFileWriter.TAG_COUNTER_EXAMPLES);
         }
         else if(ProofMetaFileWriter.TAG_COUNTER_EXAMPLE.equals(qName)){
             Object parent = parentStack.peekFirst();
             if (!ProofMetaFileWriter.TAG_COUNTER_EXAMPLES.equals(parent)) {
                 throw new SAXException(ProofMetaFileWriter.TAG_COUNTER_EXAMPLE  + " has to be a child of " + ProofMetaFileWriter.TAG_COUNTER_EXAMPLES + ".");
              }
             String id = getCounterExampleId(attributes);
             String name = getCounterExampleName(attributes);
             KeYProjectCounterExample ce = new KeYProjectCounterExample(id, name);
             counterExamples.add(ce);
             parentStack.addFirst(ce);
         }
         else if(ProofMetaFileWriter.TAG_COUNTER_EXAMPLE_NODE.equals(qName)){
             Object parent = parentStack.peekFirst();
             if (!(parent instanceof TreeElement || parent instanceof KeYProjectCounterExample)) {
                 throw new SAXException(ProofMetaFileWriter.TAG_COUNTER_EXAMPLE_NODE  + " has to be a child of " + ProofMetaFileWriter.TAG_COUNTER_EXAMPLE + "or " + ProofMetaFileWriter.TAG_COUNTER_EXAMPLE_NODE + ".");
             }
             String name = getCounterExampleNode(attributes);
             TreeElement e = new TreeElement(name);
             if(parent instanceof KeYProjectCounterExample) {
                 KeYProjectCounterExample ce = (KeYProjectCounterExample) parent;
                 ce.getModel().getTreeElements().add(e);
             }
             else if(parent instanceof TreeElement) {
                 TreeElement parentTe = (TreeElement) parent;
                 parentTe.AddChild(e);
             }
             parentStack.addFirst(e);
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
       * Returns the kjt name.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getKJT(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_KJT);
      }
      
      /**
       * Returns the source code.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getSrc(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_SRC);
      }
      
      /**
       * Returns the parameters.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getParameters(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_PARAMETERS);
      }
      

      /**
       * Returns all Implementations of a CallMethod.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getImplementations(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_IMPLEMENTATIONS);
      }
      

      /**
       * Returns a fields visibility.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getVisibility(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_VISIBILITY);
      }
      

      /**
       * Returns if a field is static.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected boolean getIsStatic(Attributes attributes) {
         return Boolean.parseBoolean(attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_IS_STATIC));
      }
      

      /**
       * Returns if a field is final.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected boolean getIsFinal(Attributes attributes) {
         return Boolean.parseBoolean(attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_IS_FINAL));
      }
      
      /**
       * Returns a fields initializer
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getInitializer(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_INITIALIZER);
      }
      
      
      /**
       * Returns the representation.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected String getRep(Attributes attributes) {
         return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_REP);
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
      
      protected String getCounterExampleId(Attributes attributes) {
          return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_COUNTER_EXAMPLE_ID);
       }
      
      protected String getCounterExampleName(Attributes attributes) {
          return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_COUNTER_EXAMPLE_NAME);
       }
      
      protected String getCounterExampleNode(Attributes attributes) {
          return attributes.getValue(ProofMetaFileWriter.ATTRIBUTE_COUNTER_EXAMPLE_NODE_NAME);
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
   
   public LinkedList<IFile> getUsedContracts(){
      return usedContracts;
   }
   
   public List<ProofMetaFileAssumption> getAssumptions() {
      return assumptions;
   }
   
   public ProofMetaReferences getReferences() {
      return references;
   }

   public List<String> getCalledMethods() {
      return calledMethods;
   }


    public List<KeYProjectCounterExample> getCounterExamples() {
        return counterExamples;
    }
}