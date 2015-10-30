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
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.sed.core.model.ISEIDElement;
import org.key_project.sed.core.model.ISELoopBodyTermination;
import org.key_project.sed.core.model.ISELoopCondition;
import org.key_project.sed.core.model.ISELoopInvariant;
import org.key_project.sed.core.model.ISELoopStatement;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodContract;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISEStatement;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.ISEValue;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.model.ISourcePathProvider;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;

/**
 * <p>
 * Instances of this class can be used to serialize an {@link ILaunch}
 * which contains only {@link ISEDebugTarget}s into a proprietary XML file.
 * It is possible to read such files via instances of {@link SEXMLReader}.
 * </p>
 * <p>
 * The main use case of the serialization is to persistent an actual
 * {@link ISEDebugTarget} as oracle file which is later used in test cases
 * to compare a given {@link ISEDebugTarget} with the loaded instance
 * of the oracle file.
 * </p>
 * @author Martin Hentschel
 * @see SEXMLReader
 */
public class SEXMLWriter {
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
    * Tag name to store {@link ISEDebugTarget}s.
    */
   public static final String TAG_DEBUG_TARGET = "sedTarget";
   
   /**
    * Tag name to store {@link ISEBranchCondition}s.
    */
   public static final String TAG_BRANCH_CONDITION = "sedBranchCondition";

   /**
    * Tag name to store {@link ISEBranchStatement}s.
    */
   public static final String TAG_BRANCH_STATEMENT = "sedBranchStatement";

   /**
    * Tag name to store {@link ISEExceptionalTermination}s.
    */
   public static final String TAG_EXCEPTIONAL_TERMINATION = "sedExceptionalTermination";

   /**
    * Tag name to store {@link ISELoopBodyTermination}s.
    */
   public static final String TAG_LOOP_BODY_TERMINATION = "sedLoopBodyTermination";

   /**
    * Tag name to store {@link ISELoopCondition}s.
    */
   public static final String TAG_LOOP_CONDITION = "sedLoopCondition";

   /**
    * Tag name to store {@link ISELoopStatement}s.
    */
   public static final String TAG_LOOP_STATEMENT = "sedLoopStatement";

   /**
    * Tag name to store {@link ISEMethodCall}s.
    */
   public static final String TAG_METHOD_CALL = "sedMethodCall";

   /**
    * Tag name to store {@link ISEMethodReturn}s.
    */
   public static final String TAG_METHOD_RETURN = "sedMethodReturn";

   /**
    * Tag name to store {@link ISEExceptionalMethodReturn}s.
    */
   public static final String TAG_EXCEPTIONAL_METHOD_RETURN = "sedExceptionalMethodReturn";

   /**
    * Tag name to store {@link ISEStatement}s.
    */
   public static final String TAG_STATEMENT = "sedStatement";

   /**
    * Tag name to store {@link ISETermination}s.
    */
   public static final String TAG_TERMINATION = "sedTermination";

   /**
    * Tag name to store {@link ISEThread}s.
    */
   public static final String TAG_THREAD = "sedThread";

   /**
    * Tag name to store {@link ISEMethodCall#getMethodReturnConditions()}.
    */
   public static final String TAG_METHOD_RETURN_CONDITIONS = "sedMethodCallMethodReturnCondition";

   /**
    * Tag name to store {@link ISENode#getGroupStartConditions()}.
    */
   public static final String TAG_GROUP_END_CONDITION_REFERENCE = "sedGroupEndConditionReference";

   /**
    * Tag name to store {@link IVariable}s.
    */
   public static final String TAG_VARIABLE = "sedVariable";

   /**
    * Tag name to store {@link IVariable}s provided by {@link ISEBaseMethodReturn#getCallStateVariables()}.
    */
   public static final String TAG_CALL_STATE_VARIABLE = "sedCallStateVariable";

   /**
    * Tag name to store {@link IValue}s.
    */
   public static final String TAG_VALUE = "sedValue";

   /**
    * Tag name to store one entry of {@link ISENode#getCallStack()}.
    */
   public static final String TAG_CALL_STACK_ENTRY = "sedCallStackEntry";

   /**
    * Tag name to store one entry of {@link ISEThread#getTerminations()}.
    */
   public static final String TAG_TERMINATION_ENTRY = "sedTerminationEntry";

   /**
    * Tag name to store a reference to an existing {@link ISENode}.
    */
   public static final String TAG_CHILD_REFERENCE = "sedChildReference";

   /**
    * Tag name to store a reference of {@link ISEGroupable#getGroupEndConditions()}.
    */
   public static final String TAG_GROUP_END_CONDITION = "sedGroupEndCondition";

   /**
    * Tag name to store {@link ISEMethodContract}s.
    */
   public static final String TAG_METHOD_CONTRACT = "sedMethodContract";

   /**
    * Tag name to store {@link ISELoopInvariant}s.
    */
   public static final String TAG_LOOP_INVARIANT = "sedLoopInvariant";

   /**
    * Tag name to store {@link ISEAnnotation}s.
    */
   public static final String TAG_ANNOTATION = "sedAnnotation";

   /**
    * Tag name to store {@link ISEAnnotationLink}s.
    */
   public static final String TAG_ANNOTATION_LINK = "sedAnnotationLink";

   /**
    * Tag name to store {@link ISEConstraint}s.
    */
   public static final String TAG_CONSTRAINT = "constraint";

   /**
    * Tag name to store relevant {@link ISEConstraint}s provided by
    * {@link ISEValue#getRelevantConstraints()}.
    */
   public static final String TAG_RELEVANT_CONSTRAINT = "relevantConstraint";

   /**
    * Attribute name to define namespaces.
    */
   public static final String ATTRIBUTE_NAMESPACE = "xmlns";

   /**
    * Attribute name to store IDs ({@link ISEIDElement#getId()}).
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
    * Refers to an existing {@link ISENode} with the defined id.
    */
   public static final String ATTRIBUTE_NODE_ID_REF = "nodeIdRef";

   /**
    * Refers to an existing {@link ISEConstraint} with the defined id.
    */
   public static final String ATTRIBUTE_CONSTRAINT_ID_REF = "constraintIdRef";

   /**
    * Attribute name to store {@link ISEMethodContract#isPreconditionComplied()}.
    */
   public static final String ATTRIBUTE_PRECONDITION_COMPLIED = "preconditionComplied";

   /**
    * Attribute name to store {@link ISEMethodContract#hasNotNullCheck()}.
    */
   public static final String ATTRIBUTE_HAS_NOT_NULL_CHECK = "hasNotNullCheck";

   /**
    * Attribute name to store {@link ISEMethodContract#isNotNullCheckComplied()}.
    */
   public static final String ATTRIBUTE_NOT_NULL_CHECK_COMPLIED = "notNullCheckComplied";

   /**
    * Attribute name to store {@link ISELoopInvariant#isInitiallyValid()}.
    */
   public static final String ATTRIBUTE_INITIALLY_VALID = "initiallyValid";

   /**
    * Attribute name to store {@link ISETermination#isVerified()}.
    */
   public static final String ATTRIBUTE_VERIFIED = "verified";

   /**
    * Attribute name to store {@link ISourcePathProvider#getSourcePath()}.
    */
   public static final String ATTRIBUTE_SOURCE_PATH = "sourcePath";

   /**
    * Attribute name to store {@link ISEAnnotationType#getTypeId()}.
    */
   public static final String ATTRIBUTE_TYPE_ID = "typeId";

   /**
    * Attribute name to store {@link ISEAnnotationType#saveAnnotation(ISEAnnotation)} and
    * {@link ISEAnnotationType#saveAnnotationLink(ISEAnnotationLink)}.
    */
   public static final String ATTRIBUTE_CONTENT = "content";

   /**
    * Attribute name to store {@link ISEAnnotation#isEnabled()}.
    */
   public static final String ATTRIBUTE_ENABLED = "enabled";

   /**
    * Attribute name to store {@link ISEAnnotation#isHighlightBackground()}.
    */
   public static final String ATTRIBUTE_HIGHLIGHT_BACKGROUND = "highlightBackground";

   /**
    * Attribute name to store {@link ISEAnnotation#getBackgroundColor()}.
    */
   public static final String ATTRIBUTE_BACKGROUND_COLOR = "backgroundColor";

   /**
    * Attribute name to store {@link ISEAnnotation#isHighlightForeground()}.
    */
   public static final String ATTRIBUTE_HIGHLIGHT_FOREGROUND = "highlightForeground";

   /**
    * Attribute name to store {@link ISEAnnotation#getForegroundColor()}.
    */
   public static final String ATTRIBUTE_FOREGROUND_COLOR = "foregroundColor";

   /**
    * Refers to an existing {@link ISEAnnotation} with the defined id.
    */
   public static final String ATTRIBUTE_ANNOTATION_LINK_SOURCE = "sourceIdRef";

   /**
    * Refers to an existing {@link ISENode} with the defined id.
    */
   public static final String ATTRIBUTE_ANNOTATION_LINK_TARGET = "targetIdRef";

   /**
    * Refers to an existing {@link ISENode} to store {@link ISEMethodReturn#getMethodReturnCondition()}.
    */
   public static final String ATTRIBUTE_METHOD_RETURN_CONDITION = "methodReturnConditionRef";

   /**
    * Attribute name to store {@link ISEGroupable#isGroupable()}.
    */
   public static final String ATTRIBUTE_GROUPABLE = "groupable";
   
   /**
    * Writes the given {@link ISEDebugTarget}s into the {@link OutputStream} with the defined encoding.
    * @param targets The {@link ISEDebugTarget}s to write.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, 
                     String encoding, 
                     OutputStream out, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     boolean saveConstraints,
                     IProgressMonitor monitor) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName(), saveVariables, saveCallStack, saveConstraints, monitor);
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
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(ILaunch launch, 
                     String encoding, 
                     OutputStream out, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     boolean saveConstraints,
                     IProgressMonitor monitor) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName(), saveVariables, saveCallStack, saveConstraints, monitor);
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
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(ILaunch launch, 
                     String encoding, 
                     IFile file, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     boolean saveConstraints,
                     IProgressMonitor monitor) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName(), saveVariables, saveCallStack, saveConstraints, monitor);
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
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, 
                     String encoding, 
                     IFile file, 
                     boolean saveVariables,
                     boolean saveCallStack,
                     boolean saveConstraints,
                     IProgressMonitor monitor) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName(), saveVariables, saveCallStack, saveConstraints, monitor);
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
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(ILaunch launch, 
                       String encoding, 
                       boolean saveVariables,
                       boolean saveCallStack,
                       boolean saveConstraints,
                       IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      if (launch != null) {
         sb.append(toXML(launch.getDebugTargets(), encoding, saveVariables, saveCallStack, saveConstraints, monitor));
      }
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link IDebugTarget}s into a {@link String} with the given encoding.
    * @param launch The {@link ILaunch} to serialize.
    * @param encoding The encoding to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(IDebugTarget[] targets, 
                       String encoding, 
                       boolean saveVariables, 
                       boolean saveCallStack,
                       boolean saveConstraints,
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
            if (target instanceof ISEDebugTarget) {
               sb.append(toXML(1, (ISEDebugTarget)target, saveVariables, saveCallStack, saveConstraints, monitor));
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
    * Serializes the given {@link ISEDebugTarget} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDebugTarget} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDebugTarget target, 
                          boolean saveVariables, 
                          boolean saveCallStack,
                          boolean saveConstraints,
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
         ISEAnnotation[] annotations = target.getRegisteredAnnotations();
         for (ISEAnnotation annotation : annotations) {
            sb.append(toXML(level + 1, annotation));
         }
         ISEThread[] threads = target.getSymbolicThreads();
         for (ISEThread thread : threads) {
            SWTUtil.checkCanceled(monitor);
            sb.append(toXML(level + 1, thread, saveVariables, saveCallStack, saveConstraints, monitor));
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
    * Serializes the given {@link ISENode} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISENode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISENode node, 
                          boolean saveVariables, 
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      if (node instanceof ISEBranchCondition) {
         return toXML(level, (ISEBranchCondition)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEBranchStatement) {
         return toXML(level, (ISEBranchStatement)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEExceptionalTermination) {
         return toXML(level, (ISEExceptionalTermination)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISELoopBodyTermination) {
         return toXML(level, (ISELoopBodyTermination)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISELoopCondition) {
         return toXML(level, (ISELoopCondition)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISELoopStatement) {
         return toXML(level, (ISELoopStatement)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEMethodCall) {
         return toXML(level, (ISEMethodCall)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEMethodReturn) {
         return toXML(level, (ISEMethodReturn)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEExceptionalMethodReturn) {
         return toXML(level, (ISEExceptionalMethodReturn)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEStatement) {
         return toXML(level, (ISEStatement)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISETermination) {
         return toXML(level, (ISETermination)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEThread) {
         return toXML(level, (ISEThread)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISEMethodContract) {
         return toXML(level, (ISEMethodContract)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else if (node instanceof ISELoopInvariant) {
         return toXML(level, (ISELoopInvariant)node, saveVariables, saveCallStack, saveConstraints, monitor);
      }
      else {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Unknown node type of node \"" + node + "\"."));
      }
   }
   
   /**
    * Serializes the given {@link ISEBranchCondition} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param branchCondition The {@link ISEBranchCondition} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEBranchCondition branchCondition, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_CONDITION, branchCondition, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEBranchStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param branchStatement The {@link ISEBranchStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEBranchStatement branchStatement, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_STATEMENT, branchStatement, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEExceptionalTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param exceptionalTermination The {@link ISEExceptionalTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEExceptionalTermination exceptionalTermination, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = createDefaultNodeAttributes(exceptionalTermination);
      attributeValues.put(ATTRIBUTE_VERIFIED, exceptionalTermination.isVerified() + "");
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_EXCEPTIONAL_TERMINATION, exceptionalTermination, saveVariables, saveCallStack, saveConstraints, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISELoopBodyTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopBodyTermination The {@link ISELoopBodyTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISELoopBodyTermination loopBodyTermination, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = createDefaultNodeAttributes(loopBodyTermination);
      attributeValues.put(ATTRIBUTE_VERIFIED, loopBodyTermination.isVerified() + "");
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_BODY_TERMINATION, loopBodyTermination, saveVariables, saveCallStack, saveConstraints, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISELoopCondition} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopCondition The {@link ISELoopCondition} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISELoopCondition loopCondition, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_CONDITION, loopCondition, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISELoopStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopStatement The {@link ISELoopStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISELoopStatement loopStatement, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_STATEMENT, loopStatement, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEMethodCall} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodCall The {@link ISEMethodCall} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEMethodCall methodCall, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_CALL, methodCall, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEMethodReturn} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodReturn The {@link ISEMethodReturn} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEMethodReturn methodReturn, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_RETURN, methodReturn, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEExceptionalMethodReturn} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodReturn The {@link ISEExceptionalMethodReturn} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEExceptionalMethodReturn methodReturn, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_EXCEPTIONAL_METHOD_RETURN, methodReturn, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param statement The {@link ISEStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEStatement statement, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_STATEMENT, statement, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEMethodContract} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodContract The {@link ISEMethodContract} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEMethodContract methodContract, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      Map<String, String> attributeValues = createDefaultNodeAttributes(methodContract);
      attributeValues.put(ATTRIBUTE_PRECONDITION_COMPLIED, methodContract.isPreconditionComplied() + "");
      attributeValues.put(ATTRIBUTE_HAS_NOT_NULL_CHECK, methodContract.hasNotNullCheck() + "");
      attributeValues.put(ATTRIBUTE_NOT_NULL_CHECK_COMPLIED, methodContract.isNotNullCheckComplied() + "");
      appendNode(level, TAG_METHOD_CONTRACT, methodContract, saveVariables, saveCallStack, saveConstraints, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISELoopInvariant} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopInvariant The {@link ISELoopInvariant} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISELoopInvariant loopInvariant, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      Map<String, String> attributeValues = createDefaultNodeAttributes(loopInvariant);
      attributeValues.put(ATTRIBUTE_INITIALLY_VALID, loopInvariant.isInitiallyValid() + "");
      appendNode(level, TAG_LOOP_INVARIANT, loopInvariant, saveVariables, saveCallStack, saveConstraints, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISETermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISETermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISETermination termination, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = createDefaultNodeAttributes(termination);
      attributeValues.put(ATTRIBUTE_VERIFIED, termination.isVerified() + "");
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_TERMINATION, termination, saveVariables, saveCallStack, saveConstraints, false, attributeValues, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEThread} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEThread} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEThread thread, 
                          boolean saveVariables,
                          boolean saveCallStack,
                          boolean saveConstraints,
                          IProgressMonitor monitor) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_THREAD, thread, saveVariables, saveCallStack, saveConstraints, false, sb, monitor);
      return sb.toString();
   }
   
   /**
    * Adds an {@link ISENode} to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param tagName The tag name to use.
    * @param node The {@link ISENode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param childrenByID {@code true} only ID of children is saved, {@code false} full child hierarchy is saved.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendNode(int level, 
                             String tagName, 
                             ISENode node, 
                             boolean saveVariables, 
                             boolean saveCallStack,
                             boolean saveConstraints,
                             boolean childrenByID,
                             StringBuffer sb, 
                             IProgressMonitor monitor) throws DebugException {
      appendNode(level, tagName, node, saveVariables, saveCallStack, saveConstraints, childrenByID, createDefaultNodeAttributes(node), sb, monitor);
   }
   
   /**
    * Creates the default {@link ISENode} attributes.
    * @param node The {@link ISENode} to save.
    * @return The created attributes.
    * @throws DebugException Occurred Exception.
    */
   protected Map<String, String> createDefaultNodeAttributes(ISENode node) throws DebugException {
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
         if (node instanceof ISEBaseMethodReturn) {
            ISEBranchCondition returnCondition = ((ISEBaseMethodReturn)node).getMethodReturnCondition();
            if (returnCondition != null) {
               attributeValues.put(ATTRIBUTE_METHOD_RETURN_CONDITION, returnCondition.getId());
            }
         }
         if (node instanceof ISEGroupable) {
            attributeValues.put(ATTRIBUTE_GROUPABLE, ((ISEGroupable) node).isGroupable() + "");
         }
      }
      return attributeValues;
   }
   
   /**
    * Adds an {@link ISENode} to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param tagName The tag name to use.
    * @param node The {@link ISENode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param childrenByID {@code true} only ID of children is saved, {@code false} full child hierarchy is saved.
    * @param attributeValues The attributes to save.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendNode(int level, 
                             String tagName, 
                             ISENode node, 
                             boolean saveVariables, 
                             boolean saveCallStack,
                             boolean saveConstraints,
                             boolean childrenByID,
                             Map<String, String> attributeValues,
                             StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      if (node != null) {
         // Append start tag
         XMLUtil.appendStartTag(level, tagName, attributeValues, sb);
         // Append constraints
         appendConstraints(level + 1, node, saveConstraints, sb, monitor);
         // Append annotation links
         ISEAnnotationLink[] links = node.getAnnotationLinks();
         for (ISEAnnotationLink link : links) {
            sb.append(toXML(level + 1, link));
         }
         // Append variables
         if (node instanceof IStackFrame) {
            appendVariables(level + 1, (IStackFrame)node, saveVariables, saveConstraints, sb, monitor);
         }
         // Append call state variables
         if (node instanceof ISEBaseMethodReturn) {
            appendCallSateVariables(level + 1, (ISEBaseMethodReturn)node, saveVariables, saveConstraints, sb, monitor);
         }
         // Append call stack
         appendCallStack(level + 1, node, saveCallStack, sb);
         // Append children
         ISENode[] children = node.getChildren();
         for (ISENode child : children) {
            SWTUtil.checkCanceled(monitor);
            if (childrenByID) {
               Map<String, String> childAttributeValues = new LinkedHashMap<String, String>();
               childAttributeValues.put(ATTRIBUTE_NODE_ID_REF, child.getId());
               XMLUtil.appendEmptyTag(level + 1, TAG_CHILD_REFERENCE, childAttributeValues, sb);               
            }
            else {
               sb.append(toXML(level + 1, child, saveVariables, saveCallStack, saveConstraints, monitor));
            }
            monitor.worked(1);
         }
         // Append method return nodes
         if (node instanceof ISEMethodCall) {
            appendMethodReturnNodes(level + 1, (ISEMethodCall)node, saveVariables, saveCallStack, saveConstraints, sb, monitor);
         }
         // Append terminations
         else if (node instanceof ISEThread) {
            appendTerminations(level + 1, (ISEThread)node, sb);
         }
         // Append group start nodes
         appendGroupStartNodes(level + 1, node, saveVariables, saveCallStack, saveConstraints, sb, monitor);
         // Append method end nodes
         if (node instanceof ISEGroupable) {
            appendGroupEndNodes(level + 1, (ISEGroupable) node, saveVariables, saveCallStack, saveConstraints, sb, monitor);
         }
         // Append end tag
         XMLUtil.appendEndTag(level, tagName, sb);
      }
   }

   /**
    * Appends the known terminations to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISEThread} which provides the known terminations.
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendTerminations(int level, ISEThread node, StringBuffer sb) throws DebugException {
      ISETermination[] terminations = node.getTerminations();
      if (terminations != null) {
         for (ISETermination termination : terminations) {
            Map<String, String> attributeValues = new LinkedHashMap<String, String>();
            attributeValues.put(ATTRIBUTE_NODE_ID_REF, termination.getId());
            XMLUtil.appendEmptyTag(level, TAG_TERMINATION_ENTRY, attributeValues, sb);
         }
      }
   }
   
   /**
    * Appends all known group start conditions.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISENode} which provides the known start conditions.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendGroupStartNodes(int level, ISENode node, boolean saveVariables, boolean saveCallStack, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      ISEBranchCondition[] conditions = node.getGroupStartConditions();
      if (conditions != null) {
         for (ISEBranchCondition condition : conditions) {
            Map<String, String> childAttributeValues = new LinkedHashMap<String, String>();
            childAttributeValues.put(ATTRIBUTE_NODE_ID_REF, condition.getId());
            XMLUtil.appendEmptyTag(level, TAG_GROUP_END_CONDITION_REFERENCE, childAttributeValues, sb);               
         }
      }
   }

   /**
    * Appends all known group end conditions.
    * @param level The level in the tree used for leading white space (formating).
    * @param node he {@link ISEGroupable} which provides the known end conditions.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendGroupEndNodes(int level, ISEGroupable node, boolean saveVariables, boolean saveCallStack, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      ISEBranchCondition[] conditions = node.getGroupEndConditions();
      if (conditions != null) {
         for (ISEBranchCondition condition : conditions) {
            appendNode(level, TAG_GROUP_END_CONDITION, condition, saveVariables, saveCallStack, saveConstraints, true, sb, monitor);
         }
      }
   }
   
   /**
    * Appends all known method returns.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISEMethodCall} which provides the known return nodes.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendMethodReturnNodes(int level, ISEMethodCall node, boolean saveVariables, boolean saveCallStack, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      ISEBranchCondition[] conditions = node.getMethodReturnConditions();
      if (conditions != null) {
         for (ISEBranchCondition condition : conditions) {
            appendNode(level, TAG_METHOD_RETURN_CONDITIONS, condition, saveVariables, saveCallStack, saveConstraints, true, sb, monitor);
         }
      }
   }

   /**
    * Appends the call stack to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISENode} which provides the call stack.
    * @param saveCallStack Save call stack?
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendCallStack(int level, ISENode node, boolean saveCallStack, StringBuffer sb) throws DebugException {
      if (saveCallStack) {
         ISENode[] callStack = node.getCallStack();
         if (callStack != null) {
            for (ISENode entry : callStack) {
               Map<String, String> attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_NODE_ID_REF, entry.getId());
               XMLUtil.appendEmptyTag(level, TAG_CALL_STACK_ENTRY, attributeValues, sb);
            }
         }
      }
   }

   /**
    * Appends all contained constraints to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param node The {@link ISENode} which contains the constraints.
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendConstraints(int level, ISENode node, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      if (saveConstraints && node.hasConstraints()) {
         ISEConstraint[] constraints = node.getConstraints();
         for (ISEConstraint constraint : constraints) {
            SWTUtil.checkCanceled(monitor);
            appendConstraint(level, constraint, sb, monitor);
            monitor.worked(1);
         }
      }
   }

   /**
    * Appends the given constraint to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param constraint The constraint to append.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendConstraint(int level, ISEConstraint constraint, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_ID, constraint.getId());
      attributeValues.put(ATTRIBUTE_NAME, constraint.getName());
      XMLUtil.appendEmptyTag(level, TAG_CONSTRAINT, attributeValues, sb);
   }

   /**
    * Appends all contained variables to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodReturn The {@link ISEBaseMethodReturn} which contains the variables.
    * @param saveVariables Save variables?
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendCallSateVariables(int level, ISEBaseMethodReturn methodReturn, boolean saveVariables, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      if (saveVariables) {
         IVariable[] variables = methodReturn.getCallStateVariables();
         if (variables != null) {
            for (IVariable variable : variables) {
               SWTUtil.checkCanceled(monitor);
               appendVariable(level, variable, saveConstraints, sb, TAG_CALL_STATE_VARIABLE, monitor);
               monitor.worked(1);
            }
         }
      }
   }

   /**
    * Appends all contained variables to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param stackFrame The {@link IStackFrame} which contains the variables.
    * @param saveVariables Save variables?
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendVariables(int level, IStackFrame stackFrame, boolean saveVariables, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      if (saveVariables && stackFrame.hasVariables()) {
         IVariable[] variables = stackFrame.getVariables();
         for (IVariable variable : variables) {
            SWTUtil.checkCanceled(monitor);
            appendVariable(level, variable, saveConstraints, sb, TAG_VARIABLE, monitor);
            monitor.worked(1);
         }
      }
   }

   /**
    * Appends the given variable to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param variable The variable to append.
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param tagName The tag name to use to store the variable.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendVariable(int level, IVariable variable, boolean saveConstraints, StringBuffer sb, String tagName, IProgressMonitor monitor) throws DebugException {
      // Append start tag
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      if (variable instanceof ISEVariable) {
         attributeValues.put(ATTRIBUTE_ID, ((ISEVariable)variable).getId());
      }
      attributeValues.put(ATTRIBUTE_NAME, variable.getName());
      attributeValues.put(ATTRIBUTE_REFERENCE_TYPE_NAME, variable.getReferenceTypeName());
      XMLUtil.appendStartTag(level, tagName, attributeValues, sb);
      // Append children
      if (variable.getValue() != null) {
         appendValue(level + 1, variable.getValue(), saveConstraints, sb, monitor);
      }
      // Append end tag
      XMLUtil.appendEndTag(level, tagName, sb);
   }

   /**
    * Appends the given value to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param value The value to append.
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendValue(int level, IValue value, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      // Append start tag
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      if (value instanceof ISEValue) {
         attributeValues.put(ATTRIBUTE_ID, ((ISEValue)value).getId());
      }
      attributeValues.put(ATTRIBUTE_REFERENCE_TYPE_NAME, value.getReferenceTypeName());
      attributeValues.put(ATTRIBUTE_VALUE_STRING, value.getValueString());
      attributeValues.put(ATTRIBUTE_ALLOCATED, value.isAllocated() + "");
      if (value instanceof ISEValue) {
         attributeValues.put(ATTRIBUTE_MULTI_VALUED, ((ISEValue)value).isMultiValued() + "");
      }
      XMLUtil.appendStartTag(level, TAG_VALUE, attributeValues, sb);
      // Append relevant constraints
      appendRelevantConstraints(level + 1, value, saveConstraints, sb, monitor);
      // Append children
      if (value.hasVariables()) {
         IVariable[] variables = value.getVariables();
         for (IVariable variable : variables) {
            SWTUtil.checkCanceled(monitor);
            appendVariable(level + 1, variable, saveConstraints, sb, TAG_VARIABLE, monitor);
            monitor.worked(1);
         }
      }
      // Append end tag
      XMLUtil.appendEndTag(level, TAG_VALUE, sb);
   }

   /**
    * Appends all relevant constraints to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param value The {@link IValue} which contains the relevant constraints.
    * @param saveConstraints Save constraints?
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendRelevantConstraints(int level, IValue value, boolean saveConstraints, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      if (saveConstraints && value instanceof ISEValue) {
         ISEConstraint[] constraints = ((ISEValue) value).getRelevantConstraints();
         if (!ArrayUtil.isEmpty(constraints)) {
            for (ISEConstraint constraint : constraints) {
               SWTUtil.checkCanceled(monitor);
               appendRelevantConstraint(level, constraint, sb, monitor);
               monitor.worked(1);
            }
         }
      }
   }

   /**
    * Appends the given relevant constraint to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param constraint The constraint to append.
    * @param sb The {@link StringBuffer} to write to.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void appendRelevantConstraint(int level, ISEConstraint constraint, StringBuffer sb, IProgressMonitor monitor) throws DebugException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_CONSTRAINT_ID_REF, constraint.getId());
      XMLUtil.appendEmptyTag(level, TAG_RELEVANT_CONSTRAINT, attributeValues, sb);
   }

   /**
    * Serializes the given {@link ISEAnnotation} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param annotation The {@link ISEAnnotation} to serialize.
    * @return The result.
    */
   protected String toXML(int level, ISEAnnotation annotation) {
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
    * Serializes the given {@link ISEAnnotationLink} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param link The {@link ISEAnnotationLink} to serialize.
    * @return The result.
    */
   protected String toXML(int level, ISEAnnotationLink link) {
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