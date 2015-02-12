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
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Set;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.Path;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * Reader for the meta files.
 * @author Stefan Käsdorf
 */
public class LastChangesFileReader {
   
   private final Set<IFile> changedJavaFiles = new LinkedHashSet<IFile>();
   private final Set<IFile> changedProofAndMetaFiles = new LinkedHashSet<IFile>();

   public Set<IFile> getChangedJavaFiles(){
      return changedJavaFiles;
   }
   
   public Set<IFile> getCHangedProofAndMetaFiles(){
      return changedProofAndMetaFiles;
   }
   
   
   /**
    * The Constructor that automatically reads the given meta{@link IFile} and Provides the content.
    * @param metaIFile
    * @throws ParserConfigurationException 
    * @throws Exception
    */
   public LastChangesFileReader(IProject project) {
      try{
         IFile lastChangesFile = KeYResourcesUtil.getProofFolder(project).getFile(KeYResourcesUtil.LAST_CHANGES_FILE);
         if(lastChangesFile.exists()){
            InputStream in = lastChangesFile.getContents();
            try {
               SAXParserFactory factory = SAXParserFactory.newInstance();
               factory.setNamespaceAware(true);
               SAXParser saxParser = factory.newSAXParser();
               LastChangesFileSAXHandler handler = new LastChangesFileSAXHandler();
               saxParser.parse(in, handler);
            }
            finally {
               in.close();
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * Utility class used by {@link LastChangesFileReader#LastChangesFileReader(IFile)}.
    */
   private class LastChangesFileSAXHandler extends DefaultHandler {      
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
         if (LastChangesFileWriter.TAG_LAST_CHANGES_FILE.equals(qName)) {
            Assert.isTrue(parentStack.isEmpty());
            parentStack.addFirst(LastChangesFileWriter.TAG_LAST_CHANGES_FILE);
         }
         else if (LastChangesFileWriter.TAG_CHANGED_JAVA_FILES.equals(qName)){
            Object parent = parentStack.peekFirst();
            if (!LastChangesFileWriter.TAG_LAST_CHANGES_FILE.equals(parent)) {
               throw new SAXException(LastChangesFileWriter.TAG_CHANGED_JAVA_FILES  + " has to be a child of " + LastChangesFileWriter.TAG_LAST_CHANGES_FILE + ".");
            }
            parentStack.addFirst(LastChangesFileWriter.TAG_CHANGED_JAVA_FILES);
         }
         else if (LastChangesFileWriter.TAG_CHANGED_JAVA_FILE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!LastChangesFileWriter.TAG_CHANGED_JAVA_FILES.equals(parent)) {
               throw new SAXException(LastChangesFileWriter.TAG_CHANGED_JAVA_FILE  + " has to be a child of " + LastChangesFileWriter.TAG_CHANGED_JAVA_FILES + ".");
            }
            changedJavaFiles.add(getChangedFile(attributes));
            parentStack.addFirst(LastChangesFileWriter.TAG_CHANGED_JAVA_FILE);
         }
         else if (LastChangesFileWriter.TAG_CHANGED_PROOF_AND_META_FILES.equals(qName)){
            Object parent = parentStack.peekFirst();
            if (!LastChangesFileWriter.TAG_LAST_CHANGES_FILE.equals(parent)) {
               throw new SAXException(LastChangesFileWriter.TAG_CHANGED_PROOF_AND_META_FILES  + " has to be a child of " + LastChangesFileWriter.TAG_LAST_CHANGES_FILE + ".");
            }
            parentStack.addFirst(LastChangesFileWriter.TAG_CHANGED_PROOF_AND_META_FILES);
         }
         else if (LastChangesFileWriter.TAG_CHANGED_PROOF_OR_META_FILE.equals(qName)) {
            Object parent = parentStack.peekFirst();
            if (!LastChangesFileWriter.TAG_CHANGED_PROOF_AND_META_FILES.equals(parent)) {
               throw new SAXException(LastChangesFileWriter.TAG_CHANGED_PROOF_OR_META_FILE  + " has to be a child of " + LastChangesFileWriter.TAG_CHANGED_PROOF_AND_META_FILES + ".");
            }
            changedProofAndMetaFiles.add(getChangedFile(attributes));
            parentStack.addFirst(LastChangesFileWriter.TAG_CHANGED_PROOF_OR_META_FILE);
         }
         else {
            throw new SAXException("Unsupported element " + qName + ".");
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) {
         if (!parentStack.isEmpty()) {
            parentStack.removeFirst();
         }
      }
      

      /**
       * Returns the path of the changed file.
       * @param attributes The attributes to read from.
       * @return The read value.
       */
      protected IFile getChangedFile(Attributes attributes) {
         String path = attributes.getValue(LastChangesFileWriter.ATTRIBUTE_FILE_PATH);
         if(path != null){
            return ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
         }
         return null;
      }
   }
}