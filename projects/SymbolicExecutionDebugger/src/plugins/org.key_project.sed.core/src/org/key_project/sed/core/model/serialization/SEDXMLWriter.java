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

package org.key_project.sed.core.model.serialization;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.Charset;
import java.util.LinkedHashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.resource.StringConverter;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchStatement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDIDElement;
import org.key_project.sed.core.model.ISEDLoopBodyTermination;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopInvariant;
import org.key_project.sed.core.model.ISEDLoopStatement;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodContract;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.model.ISourcePathProvider;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;

/**
 * <p>
 * Instances of this class can be used to serialize an {@link ILaunch}
 * which contains only {@link ISEDDebugTarget}s into a proprietary XML file.
 * It is possible to read such files via instances of {@link SEDXMLReader}.
 * </p>
 * <p>
 * The main use case of the serialization is to persistent an actual
 * {@link ISEDDebugTarget} as oracle file which is later used in test cases
 * to compare a given {@link ISEDDebugTarget} with the loaded instance
 * of the oracle file.
 * </p>
 * @author Martin Hentschel
 * @see SEDXMLReader
 */
public class SEDXMLWriter {
   /**
    * The default enconding.
    */
   public static final String DEFAULT_ENCODING = "UTF-8";
   
   /**
    * The used namespace.
    */
   public static final String NAMESPACE = "http://key-project.org/sed/serialization";
   
   /**
    * Tag name to store {@link ILaunch}s.
    */
   public static final String TAG_LAUNCH = "launch";
   
   /**
    * Tag name to store {@link ISEDDebugTarget}s.
    */
   public static final String TAG_DEBUG_TARGET = "sedTarget";
   
   /**
    * Tag name to store {@link ISEDBranchCondition}s.
    */
   public static final String TAG_BRANCH_CONDITION = "sedBranchCondition";

   /**
    * Tag name to store {@link ISEDBranchStatement}s.
    */
   public static final String TAG_BRANCH_STATEMENT = "sedBranchStatement";

   /**
    * Tag name to store {@link ISEDExceptionalTermination}s.
    */
   public static final String TAG_EXCEPTIONAL_TERMINATION = "sedExceptionalTermination";

   /**
    * Tag name to store {@link ISEDLoopBodyTermination}s.
    */
   public static final String TAG_LOOP_BODY_TERMINATION = "sedLoopBodyTermination";

   /**
    * Tag name to store {@link ISEDLoopCondition}s.
    */
   public static final String TAG_LOOP_CONDITION = "sedLoopCondition";

   /**
    * Tag name to store {@link ISEDLoopStatement}s.
    */
   public static final String TAG_LOOP_STATEMENT = "sedLoopStatement";

   /**
    * Tag name to store {@link ISEDMethodCall}s.
    */
   public static final String TAG_METHOD_CALL = "sedMethodCall";

   /**
    * Tag name to store {@link ISEDMethodReturn}s.
    */
   public static final String TAG_METHOD_RETURN = "sedMethodReturn";

   /**
    * Tag name to store {@link ISEDExceptionalMethodReturn}s.
    */
   public static final String TAG_EXCEPTIONAL_METHOD_RETURN = "sedExceptionalMethodReturn";

   /**
    * Tag name to store {@link ISEDStatement}s.
    */
   public static final String TAG_STATEMENT = "sedStatement";

   /**
    * Tag name to store {@link ISEDTermination}s.
    */
   public static final String TAG_TERMINATION = "sedTermination";

   /**
    * Tag name to store {@link ISEDThread}s.
    */
   public static final String TAG_THREAD = "sedThread";

   /**
    * Tag name to store {@link ISEDMethodCall#getMethodReturnConditions()}s.
    */
   public static final String TAG_METHOD_RETURN_CONDITIONS = "sedMethodCallMethodReturnCondition";

   /**
    * Tag name to store {@link IVariable}s.
    */
   public static final String TAG_VARIABLE = "sedVariable";

   /**
    * Tag name to store {@link IValue}s.
    */
   public static final String TAG_VALUE = "sedValue";

   /**
    * Tag name to store one entry of {@link ISEDDebugNode#getCallStack()}.
    */
   public static final String TAG_CALL_STACK_ENTRY = "sedCallStackEntry";

   /**
    * Tag name to store one entry of {@link ISEDThread#getTerminations()}.
    */
   public static final String TAG_TERMINATION_ENTRY = "sedTerminationEntry";

   /**
    * Tag name to store a reference to an existing {@link ISEDDebugNode}.
    */
   public static final String TAG_CHILD_REFERENCE = "sedChildReference";

   /**
    * Tag name to store {@link ISEDMethodContract}s.
    */
   public static final String TAG_METHOD_CONTRACT = "sedMethodContract";

   /**
    * Tag name to store {@link ISEDLoopInvariant}s.
    */
   public static final String TAG_LOOP_INVARIANT = "sedLoopInvariant";

   /**
    * Tag name to store {@link ISEDAnnotation}s.
    */
   public static final String TAG_ANNOTATION = "sedAnnotation";

   /**
    * Tag name to store {@link ISEDAnnotationLink}s.
    */
   public static final String TAG_ANNOTATION_LINK = "sedAnnotationLink";

   /**
    * Attribute name to define namespaces.
    */
   public static final String ATTRIBUTE_NAMESPACE = "xmlns";

   /**
    * Attribute name to store IDs ({@link ISEDIDElement#getId()}).
    */
   public static final String ATTRIBUTE_ID = "xml:id";

   /**
    * Attribute name to store names.
    */
   public static final String ATTRIBUTE_NAME = "name";
   
   /**
    * Attribute name to store model identifier.
    */
   public static final String ATTRIBUTE_MODEL_IDENTIFIER = "modelIdentifier";

   /**
    * Attribute name to store line numbers.
    */
   public static final String ATTRIBUTE_LINE_NUMBER = "lineNumber";

   /**
    * Attribute name to store char starts.
    */
   public static final String ATTRIBUTE_CHAR_START = "charStart";

   /**
    * Attribute name to store char ends.
    */
   public static final String ATTRIBUTE_CHAR_END = "charEnd";

   /**
    * Attribute name to store reference type names.
    */
   public static final String ATTRIBUTE_REFERENCE_TYPE_NAME = "referenceTypeName";

   /**
    * Attribute name to store value strings.
    */
   public static final String ATTRIBUTE_VALUE_STRING = "valueString";

   /**
    * Attribute name to store allocated flags.
    */
   public static final String ATTRIBUTE_ALLOCATED = "allocated";

   /**
    * Attribute name to store multi valued flags.
    */
   public static final String ATTRIBUTE_MULTI_VALUED = "multiValued";

   /**
    * Attribute name to store path conditions.
    */
   public static final String ATTRIBUTE_PATH_CONDITION = "pathCondition";

   /**
    * Refers to an existing {@link ISEDDebugNode} with the defined id.
    */
   public static final String ATTRIBUTE_NODE_ID_REF = "nodeIdRef";

   /**
    * Attribute name to store {@link ISEDMethodContract#isPreconditionComplied()}.
    */
   public static final String ATTRIBUTE_PRECONDITION_COMPLIED = "preconditionComplied";

   /**
    * Attribute name to store {@link ISEDMethodContract#hasNotNullCheck()}.
    */
   public static final String ATTRIBUTE_HAS_NOT_NULL_CHECK = "hasNotNullCheck";

   /**
    * Attribute name to store {@link ISEDMethodContract#isNotNullCheckComplied()}.
    */
   public static final String ATTRIBUTE_NOT_NULL_CHECK_COMPLIED = "notNullCheckComplied";

   /**
    * Attribute name to store {@link ISEDLoopInvariant#isInitiallyValid()}.
    */
   public static final String ATTRIBUTE_INITIALLY_VALID = "initiallyValid";

   /**
    * Attribute name to store {@link ISEDTermination#isVerified()}.
    */
   public static final String ATTRIBUTE_VERIFIED = "verified";

   /**
    * Attribute name to store {@link ISourcePathProvider#getSourcePath()}.
    */
   public static final String ATTRIBUTE_SOURCE_PATH = "sourcePath";

   /**
    * Attribute name to store {@link ISEDAnnotationType#getTypeId()}.
    */
   public static final String ATTRIBUTE_TYPE_ID = "typeId";

   /**
    * Attribute name to store {@link ISEDAnnotationType#saveAnnotation(ISEDAnnotation)} and
    * {@link ISEDAnnotationType#saveAnnotationLink(ISEDAnnotationLink)}.
    */
   public static final String ATTRIBUTE_CONTENT = "content";

   /**
    * Attribute name to store {@link ISEDAnnotation#isEnabled()}.
    */
   public static final String ATTRIBUTE_ENABLED = "enabled";

   /**
    * Attribute name to store {@link ISEDAnnotation#isHighlightBackground()}.
    */
   public static final String ATTRIBUTE_HIGHLIGHT_BACKGROUND = "highlightBackground";

   /**
    * Attribute name to store {@link ISEDAnnotation#getBackgroundColor()}.
    */
   public static final String ATTRIBUTE_BACKGROUND_COLOR = "backgroundColor";

   /**
    * Attribute name to store {@link ISEDAnnotation#isHighlightForeground()}.
    */
   public static final String ATTRIBUTE_HIGHLIGHT_FOREGROUND = "highlightForeground";

   /**
    * Attribute name to store {@link ISEDAnnotation#getForegroundColor()}.
    */
   public static final String ATTRIBUTE_FOREGROUND_COLOR = "foregroundColor";

   /**
    * Refers to an existing {@link ISEDAnnotation} with the defined id.
    */
   public static final String ATTRIBUTE_ANNOTATION_LINK_SOURCE = "sourceIdRef";

   /**
    * Refers to an existing {@link ISEDDebugNode} with the defined id.
    */
   public static final String ATTRIBUTE_ANNOTATION_LINK_TARGET = "targetIdRef";

   /**
    * Refers to an existing {@link ISEDDebugNode} to store {@link ISEDMethodReturn#getMethodReturnCondition()}.
    */
   public static final String ATTRIBUTE_METHOD_RETURN_CONDITION = "methodReturnConditionRef";
   
   /**
    * Writes the given {@link ISEDDebugTarget}s into the {@link OutputStream} with the defined encoding.
    * @param targets The {@link ISEDDebugTarget}s to write.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, 
                     String encoding, 
                     OutputStream out, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     IProgressMonitor monitor) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName(), saveVariables, saveCallStack, monitor);
            out.write(xml.getBytes(charset));
         }
         finally {
            out.close();
         }
      }
   }
   
   /**
    * Writes the given {@link ILaunch} into the {@link OutputStream} with the defined encoding.
    * @param launch The {@link ILaunch} to write.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(ILaunch launch, 
                     String encoding, 
                     OutputStream out, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     IProgressMonitor monitor) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName(), saveVariables, saveCallStack, monitor);
            out.write(xml.getBytes(charset));
         }
         finally {
            out.close();
         }
      }
   }
   
   /**
    * Writes the given {@link ILaunch} into the {@link IFile} with the defined encoding.
    * @param launch The {@link ILaunch} to write.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(ILaunch launch, 
                     String encoding, 
                     IFile file, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     IProgressMonitor monitor) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName(), saveVariables, saveCallStack, monitor);
            in = new ByteArrayInputStream(xml.getBytes(charset));
            if (file.exists()) {
               file.setContents(in, true, true, null);
            }
            else {
               file.create(in, true, null);
            }
            file.setCharset(charset.displayName(), null);
         }
         finally {
            if (in != null) {
               in.close();
            }
         }
      }
   }
   
   /**
    * Writes the given {@link IDebugTarget}s into the {@link IFile} with the defined encoding.
    * @param targets The {@link IDebugTarget}s to write.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, 
                     String encoding, 
                     IFile file, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     IProgressMonitor monitor) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName(), saveVariables, saveCallStack, monitor);
            in = new ByteArrayInputStream(xml.getBytes(charset));
            if (file.exists()) {
               file.setContents(in, true, true, null);
            }
            else {
               file.create(in, true, null);
            }
            try {
               file.setCharset(charset.displayName(), null);
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e); // Goes sometimes wrong, but is not important
            }
         }
         finally {
            if (in != null) {
               in.close();
            }
         }
      }
   }
   
   /**
    * Serializes the given {@link ILaunch} into a {@link String} with the given encoding.
    * @param launch The {@link ILaunch} to serialize.
    * @param encoding The encoding to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(ILaunch launch, 
                       String encoding, 
                       boolean saveVariables,
                       boolean saveCallStack,
                       IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      if (launch != null) {
         sb.append(toXML(launch.getDebugTargets(), encoding, saveVariables, saveCallStack, monitor));
      }
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link IDebugTarget}s into a {@link String} with the given encoding.
    * @param launch The {@link ILaunch} to serialize.
    * @param encoding The encoding to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(IDebugTarget[] targets, 
                       String encoding, 
                       boolean saveVariables, 
                       boolean saveCallStack,
                       IProgressMonitor monitor) throws DebugException {
      if (monitor == null) {
         monitor = new NullProgressMonitor();
      }
      monitor.beginTask("Convert to XML", IProgressMonitor.UNKNOWN);
      StringBuffer sb = new StringBuffer();
      if (targets != null) {
         XMLUtil.appendXmlHeader(encoding, sb);
         sb.append("<");
         sb.append(TAG_LAUNCH);
         XMLUtil.appendAttribute(ATTRIBUTE_NAMESPACE, NAMESPACE, sb);
         sb.append(">");
         XMLUtil.appendNewLine(sb);
         for (IDebugTarget target : targets) {
            SWTUtil.checkCanceled(monitor);
            if (target instanceof ISEDDebugTarget) {
               sb.append(toXML(1, (ISEDDebugTarget)target, saveVariables, saveCallStack, monitor));
            }
            else {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported debug target \"" + target + "\"."));
            }
            monitor.worked(1);
         }
         sb.append("</");
         sb.append(TAG_LAUNCH);
         sb.append(">");
         XMLUtil.appendNewLine(sb);
      }
      monitor.done();
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDDebugTarget} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDDebugTarget} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDDebugTarget target, 
                          boolean saveVariables, 
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      if (target != null) {
         XMLUtil.appendWhiteSpace(level, sb);
         sb.append("<");
         sb.append(TAG_DEBUG_TARGET);
         XMLUtil.appendAttribute(ATTRIBUTE_ID, target.getId(), sb);
         XMLUtil.appendAttribute(ATTRIBUTE_NAME, target.getName(), sb);
         XMLUtil.appendAttribute(ATTRIBUTE_MODEL_IDENTIFIER, target.getModelIdentifier(), sb);
         appenSourcePathAttribute(target, sb);
         sb.append(">");
         XMLUtil.appendNewLine(sb);
         ISEDAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEDAnnotation annotation : annotations) {
            sb.append(toXML(level + 1, annotation));
         }
         ISEDThread[] threads = target.getSymbolicThreads();
         for (ISEDThread thread : threads) {
            SWTUtil.checkCanceled(monitor);
            sb.append(toXML(level + 1, thread, saveVariables, saveCallStack, monitor));
            monitor.worked(1);
         }
         XMLUtil.appendWhiteSpace(level, sb);
         sb.append("</");
         sb.append(TAG_DEBUG_TARGET);
         sb.append(">");
         XMLUtil.appendNewLine(sb);
      }
      return sb.toString();
   }

   /**
    * Serializes the given {@link ISEDDebugNode} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDDebugNode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDDebugNode node, 
                          boolean saveVariables, 
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      if (node instanceof ISEDBranchCondition) {
         return toXML(level, (ISEDBranchCondition)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDBranchStatement) {
         return toXML(level, (ISEDBranchStatement)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDExceptionalTermination) {
         return toXML(level, (ISEDExceptionalTermination)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDLoopBodyTermination) {
         return toXML(level, (ISEDLoopBodyTermination)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDLoopCondition) {
         return toXML(level, (ISEDLoopCondition)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDLoopStatement) {
         return toXML(level, (ISEDLoopStatement)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDMethodCall) {
         return toXML(level, (ISEDMethodCall)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDMethodReturn) {
         return toXML(level, (ISEDMethodReturn)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDExceptionalMethodReturn) {
         return toXML(level, (ISEDExceptionalMethodReturn)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDStatement) {
         return toXML(level, (ISEDStatement)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDTermination) {
         return toXML(level, (ISEDTermination)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDThread) {
         return toXML(level, (ISEDThread)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDMethodContract) {
         return toXML(level, (ISEDMethodContract)node, saveVariables, saveCallStack, monitor);
      }
      else if (node instanceof ISEDLoopInvariant) {
         return toXML(level, (ISEDLoopInvariant)node, saveVariables, saveCallStack, monitor);
      }
      else {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Unknown node type of node \"" + node + "\"."));
      }
   }
   
   /**
    * Serializes the given {@link ISEDBranchCondition} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param branchCondition The {@link ISEDBranchCondition} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDBranchCondition branchCondition, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_CONDITION, branchCondition, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDBranchStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param branchStatement The {@link ISEDBranchStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDBranchStatement branchStatement, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_STATEMENT, branchStatement, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDExceptionalTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param exceptionalTermination The {@link ISEDExceptionalTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDExceptionalTermination exceptionalTermination, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = createDefaultNodeAttributes(exceptionalTermination);
      attributeValues.put(ATTRIBUTE_VERIFIED, exceptionalTermination.isVerified() + "");
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_EXCEPTIONAL_TERMINATION, exceptionalTermination, saveVariables, saveCallStack, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopBodyTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopBodyTermination The {@link ISEDLoopBodyTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopBodyTermination loopBodyTermination, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = createDefaultNodeAttributes(loopBodyTermination);
      attributeValues.put(ATTRIBUTE_VERIFIED, loopBodyTermination.isVerified() + "");
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_BODY_TERMINATION, loopBodyTermination, saveVariables, saveCallStack, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopCondition} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopCondition The {@link ISEDLoopCondition} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopCondition loopCondition, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_CONDITION, loopCondition, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopStatement The {@link ISEDLoopStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopStatement loopStatement, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_STATEMENT, loopStatement, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDMethodCall} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodCall The {@link ISEDMethodCall} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDMethodCall methodCall, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_CALL, methodCall, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDMethodReturn} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodReturn The {@link ISEDMethodReturn} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDMethodReturn methodReturn, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_RETURN, methodReturn, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDExceptionalMethodReturn} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodReturn The {@link ISEDExceptionalMethodReturn} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDExceptionalMethodReturn methodReturn, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_EXCEPTIONAL_METHOD_RETURN, methodReturn, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param statement The {@link ISEDStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDStatement statement, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_STATEMENT, statement, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDMethodContract} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodContract The {@link ISEDMethodContract} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDMethodContract methodContract, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      Map<String, String> attributeValues = createDefaultNodeAttributes(methodContract);
      attributeValues.put(ATTRIBUTE_PRECONDITION_COMPLIED, methodContract.isPreconditionComplied() + "");
      attributeValues.put(ATTRIBUTE_HAS_NOT_NULL_CHECK, methodContract.hasNotNullCheck() + "");
      attributeValues.put(ATTRIBUTE_NOT_NULL_CHECK_COMPLIED, methodContract.isNotNullCheckComplied() + "");
      appendNode(level, TAG_METHOD_CONTRACT, methodContract, saveVariables, saveCallStack, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopInvariant} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopInvariant The {@link ISEDLoopInvariant} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopInvariant loopInvariant, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      Map<String, String> attributeValues = createDefaultNodeAttributes(loopInvariant);
      attributeValues.put(ATTRIBUTE_INITIALLY_VALID, loopInvariant.isInitiallyValid() + "");
      appendNode(level, TAG_LOOP_INVARIANT, loopInvariant, saveVariables, saveCallStack, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDTermination termination, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = createDefaultNodeAttributes(termination);
      attributeValues.put(ATTRIBUTE_VERIFIED, termination.isVerified() + "");
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_TERMINATION, termination, saveVariables, saveCallStack, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDThread} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDThread} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDThread thread, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_THREAD, thread, saveVariables, saveCallStack, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Adds an {@link ISEDDebugNode} to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param tagName The tag name to use.
    * @param node The {@link ISEDDebugNode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param childrenByID {@code true} only ID of children is saved, {@code false} full child hierarchy is saved.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendNode(int level, 
                             String tagName, 
                             ISEDDebugNode node, 
                             boolean saveVariables, 
                             boolean saveCallStack,
                             boolean childrenByID,
                             StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      appendNode(level, tagName, node, saveVariables, saveCallStack, childrenByID, createDefaultNodeAttributes(node), sb, monitor);
   }
   
   /**
    * Creates the default {@link ISEDDebugNode} attributes.
    * @param node The {@link ISEDDebugNode} to save.
    * @return The created attributes.
    * @throws DebugException Occurred Exception.
    */
   protected Map<String, String> createDefaultNodeAttributes(ISEDDebugNode node) throws DebugException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      if (node != null) {
         attributeValues.put(ATTRIBUTE_ID, node.getId());
         attributeValues.put(ATTRIBUTE_NAME, node.getName());
         attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getPathCondition());
         if (node instanceof IStackFrame) {
            IStackFrame frame = (IStackFrame)node;
            attributeValues.put(ATTRIBUTE_LINE_NUMBER, frame.getLineNumber() + "");
            attributeValues.put(ATTRIBUTE_CHAR_START, frame.getCharStart() + "");
            attributeValues.put(ATTRIBUTE_CHAR_END, frame.getCharEnd() + "");
         }
         if (node instanceof ISourcePathProvider) {
            attributeValues.put(ATTRIBUTE_SOURCE_PATH, ((ISourcePathProvider)node).getSourcePath());
         }
         if (node instanceof ISEDBaseMethodReturn) {
            ISEDBranchCondition returnCondition = ((ISEDBaseMethodReturn)node).getMethodReturnCondition();
            if (returnCondition != null) {
               attributeValues.put(ATTRIBUTE_METHOD_RETURN_CONDITION, returnCondition.getId());
            }
         }
      }
      return attributeValues;
   }
   
   /**
    * Adds an {@link ISEDDebugNode} to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param tagName The tag name to use.
    * @param node The {@link ISEDDebugNode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param childrenByID {@code true} only ID of children is saved, {@code false} full child hierarchy is saved.
    * @param attributeValues The attributes to save.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendNode(int level, 
                             String tagName, 
                             ISEDDebugNode node, 
                             boolean saveVariables, 
                             boolean saveCallStack,
                             boolean childrenByID,
                             Map<String, String> attributeValues,
                             StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      if (node != null) {
         // Append start tag
         XMLUtil.appendStartTag(level, tagName, attributeValues, sb);
         // Append annotation links
         ISEDAnnotationLink[] links = node.getAnnotationLinks();
         for (ISEDAnnotationLink link : links) {
            sb.append(toXML(level + 1, link));
         }
         // Append variables
         if (node instanceof IStackFrame) {
            appendVariables(level + 1, (IStackFrame)node, saveVariables, sb, monitor);
         }
         // Append call stack
         appendCallStack(level + 1, node, saveCallStack, sb);
         // Append children
         ISEDDebugNode[] children = node.getChildren();
         for (ISEDDebugNode child : children) {
            SWTUtil.checkCanceled(monitor);
            if (childrenByID) {
               Map<String, String> childAttributeValues = new LinkedHashMap<String, String>();
               childAttributeValues.put(ATTRIBUTE_NODE_ID_REF, child.getId());
               XMLUtil.appendEmptyTag(level + 1, TAG_CHILD_REFERENCE, childAttributeValues, sb);               
            }
            else {
               sb.append(toXML(level + 1, child, saveVariables, saveCallStack, monitor));
            }
            monitor.worked(1);
         }
         // Append method return nodes
         if (node instanceof ISEDMethodCall) {
            appendMethodReturnNodes(level + 1, (ISEDMethodCall)node, saveVariables, saveCallStack, sb, monitor);
         }
         // Append terminations
         else if (node instanceof ISEDThread) {
            appendTerminations(level + 1, (ISEDThread)node, sb);
         }
         // Append end tag
         XMLUtil.appendEndTag(level, tagName, sb);
      }
   }

   /**
    * Appends the known terminations to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISEDThread} which provides the known terminations.
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendTerminations(int level, ISEDThread node, StringBuffer sb) throws DebugException {
      ISEDTermination[] terminations = node.getTerminations();
      if (terminations != null) {
         for (ISEDTermination termination : terminations) {
            Map<String, String> attributeValues = new LinkedHashMap<String, String>();
            attributeValues.put(ATTRIBUTE_NODE_ID_REF, termination.getId());
            XMLUtil.appendEmptyTag(level, TAG_TERMINATION_ENTRY, attributeValues, sb);
         }
      }
   }
   
   /**
    * Appends all known method returns.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISEDMethodCall} which provides the known return nodes.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendMethodReturnNodes(int level, ISEDMethodCall node, boolean saveVariables, boolean saveCallStack, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      ISEDBranchCondition[] conditions = node.getMethodReturnConditions();
      if (conditions != null) {
         for (ISEDBranchCondition condition : conditions) {
            appendNode(level, TAG_METHOD_RETURN_CONDITIONS, condition, saveVariables, saveCallStack, true, sb, monitor);
         }
      }
   }

   /**
    * Appends the call stack to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISEDDebugNode} which provides the call stack.
    * @param saveCallStack Save call stack?
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendCallStack(int level, ISEDDebugNode node, boolean saveCallStack, StringBuffer sb) throws DebugException {
      if (saveCallStack) {
         ISEDDebugNode[] callStack = node.getCallStack();
         if (callStack != null) {
            for (ISEDDebugNode entry : callStack) {
               Map<String, String> attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_NODE_ID_REF, entry.getId());
               XMLUtil.appendEmptyTag(level, TAG_CALL_STACK_ENTRY, attributeValues, sb);
            }
         }
      }
   }

   /**
    * Appends all contained variables to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param stackFrame The {@link IStackFrame} which contains the variables.
    * @param saveVariables Save variables?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendVariables(int level, IStackFrame stackFrame, boolean saveVariables, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      if (saveVariables && stackFrame.hasVariables()) {
         IVariable[] variables = stackFrame.getVariables();
         for (IVariable variable : variables) {
            SWTUtil.checkCanceled(monitor);
            appendVariable(level, variable, sb, monitor);
            monitor.worked(1);
         }
      }
   }

   /**
    * Appends the given variable to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param variable The variable to append.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendVariable(int level, IVariable variable, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      // Append start tag
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      if (variable instanceof ISEDVariable) {
         attributeValues.put(ATTRIBUTE_ID, ((ISEDVariable)variable).getId());
      }
      attributeValues.put(ATTRIBUTE_NAME, variable.getName());
      attributeValues.put(ATTRIBUTE_REFERENCE_TYPE_NAME, variable.getReferenceTypeName());
      XMLUtil.appendStartTag(level, TAG_VARIABLE, attributeValues, sb);
      // Append children
      if (variable.getValue() != null) {
         appendValue(level + 1, variable.getValue(), sb, monitor);
      }
      // Append end tag
      XMLUtil.appendEndTag(level, TAG_VARIABLE, sb);
   }

   /**
    * Appends the given value to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param value The value to append.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendValue(int level, IValue value, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      // Append start tag
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      if (value instanceof ISEDValue) {
         attributeValues.put(ATTRIBUTE_ID, ((ISEDValue)value).getId());
      }
      attributeValues.put(ATTRIBUTE_REFERENCE_TYPE_NAME, value.getReferenceTypeName());
      attributeValues.put(ATTRIBUTE_VALUE_STRING, value.getValueString());
      attributeValues.put(ATTRIBUTE_ALLOCATED, value.isAllocated() + "");
      if (value instanceof ISEDValue) {
         attributeValues.put(ATTRIBUTE_MULTI_VALUED, ((ISEDValue)value).isMultiValued() + "");
      }
      XMLUtil.appendStartTag(level, TAG_VALUE, attributeValues, sb);
      // Append children
      if (value.hasVariables()) {
         IVariable[] variables = value.getVariables();
         for (IVariable variable : variables) {
            SWTUtil.checkCanceled(monitor);
            appendVariable(level + 1, variable, sb, monitor);
            monitor.worked(1);
         }
      }
      // Append end tag
      XMLUtil.appendEndTag(level, TAG_VALUE, sb);
   }

   /**
    * Serializes the given {@link ISEDAnnotation} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param annotation The {@link ISEDAnnotation} to serialize.
    * @return The result.
    */
   protected String toXML(int level, ISEDAnnotation annotation) {
      StringBuffer sb = new StringBuffer();
      if (annotation != null) {
         Map<String, String> attributeValues = new LinkedHashMap<String, String>();
         attributeValues.put(ATTRIBUTE_ID, annotation.getId());
         attributeValues.put(ATTRIBUTE_TYPE_ID, annotation.getType().getTypeId());
         attributeValues.put(ATTRIBUTE_ENABLED, annotation.isEnabled() + "");
         attributeValues.put(ATTRIBUTE_HIGHLIGHT_BACKGROUND, annotation.isHighlightBackground() + "");
         attributeValues.put(ATTRIBUTE_BACKGROUND_COLOR, StringConverter.asString(annotation.getBackgroundColor()));
         attributeValues.put(ATTRIBUTE_HIGHLIGHT_FOREGROUND, annotation.isHighlightForeground() + "");
         attributeValues.put(ATTRIBUTE_FOREGROUND_COLOR, StringConverter.asString(annotation.getForegroundColor()));
         String savedContent = annotation.getType().saveAnnotation(annotation);
         if (!StringUtil.isTrimmedEmpty(savedContent)) {
            attributeValues.put(ATTRIBUTE_CONTENT, XMLUtil.encodeText(savedContent));
         }
         XMLUtil.appendEmptyTag(level, TAG_ANNOTATION, attributeValues, sb);
      }
      return sb.toString();
   }

   /**
    * Serializes the given {@link ISEDAnnotationLink} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param link The {@link ISEDAnnotationLink} to serialize.
    * @return The result.
    */
   protected String toXML(int level, ISEDAnnotationLink link) {
      StringBuffer sb = new StringBuffer();
      if (link != null) {
         Map<String, String> attributeValues = new LinkedHashMap<String, String>();
         attributeValues.put(ATTRIBUTE_ID, link.getId());
         attributeValues.put(ATTRIBUTE_ANNOTATION_LINK_SOURCE, link.getSource().getId());
         attributeValues.put(ATTRIBUTE_ANNOTATION_LINK_TARGET, link.getTarget().getId());
         String savedContent = link.getSource().getType().saveAnnotationLink(link);
         if (!StringUtil.isTrimmedEmpty(savedContent)) {
            attributeValues.put(ATTRIBUTE_CONTENT, XMLUtil.encodeText(savedContent));
         }
         XMLUtil.appendEmptyTag(level, TAG_ANNOTATION_LINK, attributeValues, sb);
      }
      return sb.toString();
   }

   /**
    * Appends the attribute to store {@link ISourcePathProvider#getSourcePath()} if available.
    * @param object The {@link Object} to save its source path.
    * @param sb The {@link StringBuffer} to write to.
    */
   protected void appenSourcePathAttribute(Object object, StringBuffer sb) {
      if (object instanceof ISourcePathProvider) {
         XMLUtil.appendAttribute(ATTRIBUTE_SOURCE_PATH, ((ISourcePathProvider) object).getSourcePath(), sb);
      }
   }
}