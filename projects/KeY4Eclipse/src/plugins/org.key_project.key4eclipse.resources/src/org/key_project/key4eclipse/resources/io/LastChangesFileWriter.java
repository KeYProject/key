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

import java.io.ByteArrayInputStream;
import java.nio.charset.Charset;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourceAttributes;
import org.key_project.key4eclipse.resources.builder.ProofElement;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.java.XMLUtil;

import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Writer for the meta files.
 * @author Stefan Käsdorf
 */
public class LastChangesFileWriter {
   
   public static final String TAG_LAST_CHANGES_FILE = "lastChangesFile";
   public static final String TAG_CHANGED_JAVA_FILES = "changedJavaFiles";
   public static final String TAG_CHANGED_PROOF_AND_META_FILES = "changedProofAndMetaFiles";
   public static final String TAG_CHANGED_JAVA_FILE = "changedJavaFile";
   public static final String TAG_CHANGED_PROOF_OR_META_FILE = "changedProofOrMetaFile";
   public static final String ATTRIBUTE_FILE_PATH = "path";

   /**
    * Forbid instances.
    */
   private LastChangesFileWriter() {
   }
   
   
   public static void resetLastChangesFiles(IProject project) {
      writeLastChangesFile(project, new HashSet<IFile>(), new HashSet<IFile>());
   }
   
   
   /**
    * Creates the meta file for the given {@link ProofElement}.
    * @param pe - the {@link ProofElement} to use
    * @throws Exception
    */
   public static void writeLastChangesFile(IProject project, Set<IFile> changedJavaFiles, Set<IFile> changedProofAndMetaFiles)  {
      if(changedJavaFiles != null && changedProofAndMetaFiles != null){
         try{
            IFile lastChangesFile = KeYResourcesUtil.getProofFolder(project).getFile(KeYResourcesUtil.LAST_CHANGES_FILE);
            String encoding = Charset.defaultCharset().name();
            String xml = toXml(changedJavaFiles, changedProofAndMetaFiles, encoding);
            KeYResourcesUtil.createFolder(lastChangesFile);
            if(!lastChangesFile.exists()){
               lastChangesFile.create(new ByteArrayInputStream(xml.getBytes(encoding)), true, null);
            }
            else {
               // Make sure that file is not read-only for compatibility with older relases. But do not set read-only flag because it requires admin rights on Mac OS to delete it.
               if (lastChangesFile.isReadOnly()) {
                  ResourceAttributes resAttr = lastChangesFile.getResourceAttributes();
                  resAttr.setReadOnly(false);
                  lastChangesFile.setResourceAttributes(resAttr);
               }
               lastChangesFile.setContents(new ByteArrayInputStream(xml.getBytes(encoding)), true, true, null);
            }
         } catch (Exception e){
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   private static String toXml(Set<IFile> changedJavaFiles, Set<IFile> changedProofAndMetaFiles, String encoding) {
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(encoding, sb);;
      XMLUtil.appendStartTag(0, TAG_LAST_CHANGES_FILE, null, sb);
      appendChangedJavaFiles(1, changedJavaFiles, sb);
      appendChangedProofAndMetaFiles(1, changedProofAndMetaFiles, sb);
      XMLUtil.appendEndTag(0, TAG_LAST_CHANGES_FILE, sb);
      return sb.toString();
   }
   
   private static void appendChangedJavaFiles(int level, Set<IFile> changedJavaFiles, StringBuffer sb){
      XMLUtil.appendStartTag(level, TAG_CHANGED_JAVA_FILES, null, sb);
      for(IFile file : changedJavaFiles){
         Map<String, String> subAttributeValues = new LinkedHashMap<String, String>();
         subAttributeValues.put(ATTRIBUTE_FILE_PATH, file.getFullPath().toString());
         XMLUtil.appendEmptyTag(level + 1, TAG_CHANGED_JAVA_FILE, subAttributeValues, sb);
      }
      XMLUtil.appendEndTag(level, TAG_CHANGED_JAVA_FILES, sb);
   }
   
   private static void appendChangedProofAndMetaFiles(int level, Set<IFile> changedProofFiles, StringBuffer sb){
      XMLUtil.appendStartTag(level, TAG_CHANGED_PROOF_AND_META_FILES, null, sb);
      for(IFile file : changedProofFiles){
         Map<String, String> subAttributeValues = new LinkedHashMap<String, String>();
         subAttributeValues.put(ATTRIBUTE_FILE_PATH, file.getFullPath().toString());
         XMLUtil.appendEmptyTag(level + 1, TAG_CHANGED_PROOF_OR_META_FILE, subAttributeValues, sb);
      }
      XMLUtil.appendEndTag(level, TAG_CHANGED_PROOF_AND_META_FILES, sb);
   }
}