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
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.java.XMLUtil;

import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Writer for the lastChangesFile.
 * @author Stefan Käsdorf
 */
public class LastChangesFileWriter {

   public static final String TAG_BUILD_STATE = "buildState";
   public static final String TAG_LAST_CHANGES_FILE = "lastChangesFile";
   public static final String TAG_CHANGED_JAVA_FILES = "changedJavaFiles";
   public static final String TAG_CHANGED_PROOF_AND_META_FILES = "changedProofAndMetaFiles";
   public static final String TAG_CHANGED_JAVA_FILE = "changedJavaFile";
   public static final String TAG_CHANGED_PROOF_OR_META_FILE = "changedProofOrMetaFile";
   public static final String ATTRIBUTE_FILE_PATH = "path";
   public static final String ATTRIBUTE_IS_BUILDING = "isBuilding";

   /**
    * Forbid instances.
    */
   private LastChangesFileWriter() {
   }

   
   /**
    * Updates the build state of the file. Changed files are untouched.
    * @param project the particular {@link IProject}
    * @param buildState the new build state
    */
   public static void updateBuildState(IProject project, boolean buildState){
      LastChangesFileReader lcfr = new LastChangesFileReader(project);
      writeLastChangesFile(project, buildState, lcfr.getChangedJavaFiles(), lcfr.getCHangedProofAndMetaFiles());
   }
   
   /**
    * Creates the lastChangesFile
    * @param project the particular {@link IProject}
    * @param buildState the build state
    * @param changedJavaFiles changed java files
    * @param changedProofAndMetaFiles changed proof and meta files
    * @throws Exception
    */
   public static void writeLastChangesFile(IProject project, boolean buildState, Set<IFile> changedJavaFiles, Set<IFile> changedProofAndMetaFiles)  {
      if(changedJavaFiles != null && changedProofAndMetaFiles != null){
         try{
            IFile lastChangesFile = KeYResourcesUtil.getProofFolder(project).getFile(KeYResourcesUtil.LAST_CHANGES_FILE);
            String encoding = Charset.defaultCharset().name();
            String xml = toXml(buildState, changedJavaFiles, changedProofAndMetaFiles, encoding);
            KeYResourcesUtil.createFolder(lastChangesFile);
            if(!lastChangesFile.exists()){
               lastChangesFile.create(new ByteArrayInputStream(xml.getBytes(encoding)), true, null);
            }
            else {
               lastChangesFile.setContents(new ByteArrayInputStream(xml.getBytes(encoding)), true, true, null);
            }
         } catch (Exception e){
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   
   private static String toXml(boolean buildState, Set<IFile> changedJavaFiles, Set<IFile> changedProofAndMetaFiles, String encoding) {
      StringBuffer sb = new StringBuffer();
      XMLUtil.appendXmlHeader(encoding, sb);;
      XMLUtil.appendStartTag(0, TAG_LAST_CHANGES_FILE, null, sb);
      appendIsBuilding(1, buildState, sb);
      appendChangedJavaFiles(1, changedJavaFiles, sb);
      appendChangedProofAndMetaFiles(1, changedProofAndMetaFiles, sb);
      XMLUtil.appendEndTag(0, TAG_LAST_CHANGES_FILE, sb);
      return sb.toString();
   }
   
   
   private static void appendIsBuilding(int level, boolean buildState, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_IS_BUILDING, String.valueOf(buildState));
      XMLUtil.appendEmptyTag(level, TAG_BUILD_STATE, attributeValues, sb);
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