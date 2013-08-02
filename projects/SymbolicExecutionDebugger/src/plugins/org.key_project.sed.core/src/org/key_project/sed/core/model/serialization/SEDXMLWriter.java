/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchStatement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDLoopBodyTermination;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopStatement;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDLoopInvariant;
import org.key_project.sed.core.model.ISEDOperationContract;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.util.LogUtil;
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
    * The used leading white space in each level.
    */
   public static final String LEADING_WHITE_SPACE_PER_LEVEL = "   ";
   
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
    * Tag name to store {@link ISEDOperationContract}s.
    */
   public static final String TAG_OPERATION_CONTRACT = "sedOperationContract";

   /**
    * Tag name to store {@link ISEDLoopInvariant}s.
    */
   public static final String TAG_LOOP_INVARIANT = "sedLoopInvariant";

   /**
    * Attribute name to store encodings.
    */
   private static final String ATTRIBUTE_ENCODING = "encoding";

   /**
    * Attribute name to define namespaces.
    */
   public static final String ATTRIBUTE_NAMESPACE = "xmlns";

   /**
    * Attribute name to store IDs.
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
    * Attribute name to store {@link ISEDOperationContract#isPreconditionComplied()}.
    */
   public static final String ATTRIBUTE_PRECONDITION_COMPLIED = "preconditionComplied";

   /**
    * Attribute name to store {@link ISEDOperationContract#hasNotNullCheck()}.
    */
   public static final String ATTRIBUTE_HAS_NOT_NULL_CHECK = "hasNotNullCheck";

   /**
    * Attribute name to store {@link ISEDOperationContract#isNotNullCheckComplied()}.
    */
   public static final String ATTRIBUTE_NOT_NULL_CHECK_COMPLIED = "notNullCheckComplied";

   /**
    * Attribute name to store {@link ISEDLoopInvariant#isInitiallyValid()}.
    */
   public static final String ATTRIBUTE_INITIALLY_VALID = "initiallyValid";
   
   /**
    * Writes the given {@link ISEDDebugTarget}s into the {@link OutputStream} with the defined encoding.
    * @param targets The {@link ISEDDebugTarget}s to write.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, 
                     String encoding, 
                     OutputStream out, 
                     boolean saveVariables,
                     boolean saveCallStack) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName(), saveVariables, saveCallStack);
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
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(ILaunch launch, 
                     String encoding, 
                     OutputStream out, 
                     boolean saveVariables,
                     boolean saveCallStack) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName(), saveVariables, saveCallStack);
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
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(ILaunch launch, 
                     String encoding, 
                     IFile file, 
                     boolean saveVariables,
                     boolean saveCallStack) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName(), saveVariables, saveCallStack);
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
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, 
                     String encoding, 
                     IFile file, 
                     boolean saveVariables,
                     boolean saveCallStack) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName(), saveVariables, saveCallStack);
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
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(ILaunch launch, 
                       String encoding, 
                       boolean saveVariables,
                       boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      if (launch != null) {
         sb.append(toXML(launch.getDebugTargets(), encoding, saveVariables, saveCallStack));
      }
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link IDebugTarget}s into a {@link String} with the given encoding.
    * @param launch The {@link ILaunch} to serialize.
    * @param encoding The encoding to use.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(IDebugTarget[] targets, 
                       String encoding, 
                       boolean saveVariables, 
                       boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      if (targets != null) {
         appendXmlHeader(encoding, sb);
         sb.append("<");
         sb.append(TAG_LAUNCH);
         appendAttribute(ATTRIBUTE_NAMESPACE, NAMESPACE, sb);
         sb.append(">");
         appendNewLine(sb);
         for (IDebugTarget target : targets) {
            if (target instanceof ISEDDebugTarget) {
               sb.append(toXML(1, (ISEDDebugTarget)target, saveVariables, saveCallStack));
            }
            else {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported debug target \"" + target + "\"."));
            }
         }
         sb.append("</");
         sb.append(TAG_LAUNCH);
         sb.append(">");
         appendNewLine(sb);
      }
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDDebugTarget} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDDebugTarget} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDDebugTarget target, 
                          boolean saveVariables, 
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      if (target != null) {
         appendWhiteSpace(level, sb);
         sb.append("<");
         sb.append(TAG_DEBUG_TARGET);
         appendAttribute(ATTRIBUTE_ID, target.getId(), sb);
         appendAttribute(ATTRIBUTE_NAME, target.getName(), sb);
         appendAttribute(ATTRIBUTE_MODEL_IDENTIFIER, target.getModelIdentifier(), sb);
         sb.append(">");
         appendNewLine(sb);
         ISEDThread[] threads = target.getSymbolicThreads();
         for (ISEDThread thread : threads) {
            sb.append(toXML(level + 1, thread, saveVariables, saveCallStack));
         }
         appendWhiteSpace(level, sb);
         sb.append("</");
         sb.append(TAG_DEBUG_TARGET);
         sb.append(">");
         appendNewLine(sb);
      }
      return sb.toString();
   }

   /**
    * Serializes the given {@link ISEDDebugNode} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDDebugNode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDDebugNode node, 
                          boolean saveVariables, 
                          boolean saveCallStack) throws DebugException {
      if (node instanceof ISEDBranchCondition) {
         return toXML(level, (ISEDBranchCondition)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDBranchStatement) {
         return toXML(level, (ISEDBranchStatement)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDExceptionalTermination) {
         return toXML(level, (ISEDExceptionalTermination)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDLoopBodyTermination) {
         return toXML(level, (ISEDLoopBodyTermination)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDLoopCondition) {
         return toXML(level, (ISEDLoopCondition)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDLoopStatement) {
         return toXML(level, (ISEDLoopStatement)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDMethodCall) {
         return toXML(level, (ISEDMethodCall)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDMethodReturn) {
         return toXML(level, (ISEDMethodReturn)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDStatement) {
         return toXML(level, (ISEDStatement)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDTermination) {
         return toXML(level, (ISEDTermination)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDThread) {
         return toXML(level, (ISEDThread)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDOperationContract) {
         return toXML(level, (ISEDOperationContract)node, saveVariables, saveCallStack);
      }
      else if (node instanceof ISEDLoopInvariant) {
         return toXML(level, (ISEDLoopInvariant)node, saveVariables, saveCallStack);
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
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDBranchCondition branchCondition, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_CONDITION, branchCondition, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDBranchStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param branchStatement The {@link ISEDBranchStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDBranchStatement branchStatement, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_STATEMENT, branchStatement, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDExceptionalTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param exceptionalTermination The {@link ISEDExceptionalTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDExceptionalTermination exceptionalTermination, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_EXCEPTIONAL_TERMINATION, exceptionalTermination, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopBodyTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopBodyTermination The {@link ISEDLoopBodyTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopBodyTermination loopBodyTermination, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_BODY_TERMINATION, loopBodyTermination, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopCondition} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopCondition The {@link ISEDLoopCondition} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopCondition loopCondition, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_CONDITION, loopCondition, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopStatement The {@link ISEDLoopStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopStatement loopStatement, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_STATEMENT, loopStatement, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDMethodCall} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodCall The {@link ISEDMethodCall} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDMethodCall methodCall, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_CALL, methodCall, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDMethodReturn} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param methodReturn The {@link ISEDMethodReturn} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDMethodReturn methodReturn, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_RETURN, methodReturn, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param statement The {@link ISEDStatement} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDStatement statement, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_STATEMENT, statement, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDOperationContract} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param operationContract The {@link ISEDOperationContract} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDOperationContract operationContract, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      Map<String, String> attributeValues = createDefaultNodeAttributes(operationContract);
      attributeValues.put(ATTRIBUTE_PRECONDITION_COMPLIED, operationContract.isPreconditionComplied() + "");
      attributeValues.put(ATTRIBUTE_HAS_NOT_NULL_CHECK, operationContract.hasNotNullCheck() + "");
      attributeValues.put(ATTRIBUTE_NOT_NULL_CHECK_COMPLIED, operationContract.isNotNullCheckComplied() + "");
      appendNode(level, TAG_OPERATION_CONTRACT, operationContract, saveVariables, saveCallStack, attributeValues, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopInvariant} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param loopInvariant The {@link ISEDLoopInvariant} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDLoopInvariant loopInvariant, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      Map<String, String> attributeValues = createDefaultNodeAttributes(loopInvariant);
      attributeValues.put(ATTRIBUTE_INITIALLY_VALID, loopInvariant.isInitiallyValid() + "");
      appendNode(level, TAG_LOOP_INVARIANT, loopInvariant, saveVariables, saveCallStack, attributeValues, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDTermination} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDTermination termination, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_TERMINATION, termination, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDThread} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDThread} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, 
                          ISEDThread thread, 
                          boolean saveVariables,
                          boolean saveCallStack) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_THREAD, thread, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Adds an {@link ISEDDebugNode} to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param tagName The tag name to use.
    * @param node The {@link ISEDDebugNode} to serialize.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendNode(int level, 
                             String tagName, 
                             ISEDDebugNode node, 
                             boolean saveVariables, 
                             boolean saveCallStack,
                             StringBuffer sb) throws DebugException {
      appendNode(level, tagName, node, saveVariables, saveCallStack, createDefaultNodeAttributes(node), sb);
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
    * @param attributeValues The attributes to save.
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendNode(int level, 
                             String tagName, 
                             ISEDDebugNode node, 
                             boolean saveVariables, 
                             boolean saveCallStack,
                             Map<String, String> attributeValues,
                             StringBuffer sb) throws DebugException {
      if (node != null) {
         // Append start tag
         appendStartTag(level, tagName, attributeValues, sb);
         // Append variables
         if (node instanceof IStackFrame) {
            appendVariables(level + 1, (IStackFrame)node, saveVariables, sb);
         }
         // Append call stack
         appendCallStack(level + 1, node, saveCallStack, sb);
         // Append children
         ISEDDebugNode[] children = node.getChildren();
         for (ISEDDebugNode child : children) {
            sb.append(toXML(level + 1, child, saveVariables, saveCallStack));
         }
         // Append end tag
         appendEndTag(level, tagName, sb);
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
               appendEmptyTag(level, TAG_CALL_STACK_ENTRY, attributeValues, sb);
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
    * @throws DebugException Occurred Exception.
    */
   protected void appendVariables(int level, IStackFrame stackFrame, boolean saveVariables, StringBuffer sb) throws DebugException {
      if (saveVariables && stackFrame.hasVariables()) {
         IVariable[] variables = stackFrame.getVariables();
         for (IVariable variable : variables) {
            appendVariable(level, variable, sb);
         }
      }
   }

   /**
    * Appends the given variable to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param variable The variable to append.
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendVariable(int level, IVariable variable, StringBuffer sb) throws DebugException {
      // Append start tag
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      if (variable instanceof ISEDVariable) {
         attributeValues.put(ATTRIBUTE_ID, ((ISEDVariable)variable).getId());
      }
      attributeValues.put(ATTRIBUTE_NAME, variable.getName());
      attributeValues.put(ATTRIBUTE_REFERENCE_TYPE_NAME, variable.getReferenceTypeName());
      appendStartTag(level, TAG_VARIABLE, attributeValues, sb);
      // Append children
      if (variable.getValue() != null) {
         appendValue(level + 1, variable.getValue(), sb);
      }
      // Append end tag
      appendEndTag(level, TAG_VARIABLE, sb);
   }

   /**
    * Appends the given value to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param value The value to append.
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendValue(int level, IValue value, StringBuffer sb) throws DebugException {
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
      appendStartTag(level, TAG_VALUE, attributeValues, sb);
      // Append children
      if (value.hasVariables()) {
         IVariable[] variables = value.getVariables();
         for (IVariable variable : variables) {
            appendVariable(level + 1, variable, sb);
         }
      }
      // Append end tag
      appendEndTag(level, TAG_VALUE, sb);
   }

   /**
    * Appends an empty tag to the given {@link StringBuffer}.
    * @param level The level.
    * @param tagName The tag name.
    * @param attributeValues The attributes.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendEmptyTag(int level, String tagName, Map<String, String> attributeValues, StringBuffer sb) {
      appendWhiteSpace(level, sb);
      sb.append("<");
      sb.append(tagName);
      for (Entry<String, String> entry : attributeValues.entrySet()) {
         appendAttribute(entry.getKey(), entry.getValue(), sb);
      }
      sb.append("/>");
      appendNewLine(sb);
   }

   /**
    * Appends a start tag to the given {@link StringBuffer}.
    * @param level The level.
    * @param tagName The tag name.
    * @param attributeValues The attributes.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendStartTag(int level, String tagName, Map<String, String> attributeValues, StringBuffer sb) {
      appendWhiteSpace(level, sb);
      sb.append("<");
      sb.append(tagName);
      for (Entry<String, String> entry : attributeValues.entrySet()) {
         appendAttribute(entry.getKey(), entry.getValue(), sb);
      }
      sb.append(">");
      appendNewLine(sb);
   }

   /**
    * Appends an end tag to the given {@link StringBuffer}.
    * @param level The level.
    * @param tagName The tag name.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendEndTag(int level, String tagName, StringBuffer sb) {
      appendWhiteSpace(level, sb);
      sb.append("</");
      sb.append(tagName);
      sb.append(">");
      appendNewLine(sb);
   }

   /**
    * Adds leading white space to the {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param sb The {@link StringBuffer} to write to.
    */
   protected void appendWhiteSpace(int level, StringBuffer sb) {
      for (int i = 0; i < level; i++) {
         sb.append(LEADING_WHITE_SPACE_PER_LEVEL);
      }
   }
   
   /**
    * Adds an XML attribute to the given {@link StringBuffer}.
    * @param attributeName The attribute name.
    * @param value The attribute value.
    * @param sb The {@link StringBuffer} to write to.
    */
   protected void appendAttribute(String attributeName, String value, StringBuffer sb) {
      if (attributeName != null && value != null) {
         sb.append(" ");
         sb.append(attributeName);
         sb.append("=\"");
         sb.append(XMLUtil.encodeText(value));
         sb.append("\"");
      }
   }
   
   /**
    * Adds an XML header to the given {@link StringBuffer}.
    * @param encoding The encoding to use.
    * @param sb The {@link StringBuffer} to write to.
    */
   protected void appendXmlHeader(String encoding, StringBuffer sb) {
      sb.append("<?xml version=\"1.0\"");
      appendAttribute(ATTRIBUTE_ENCODING, encoding, sb);
      sb.append("?>");
      appendNewLine(sb);
   }
   
   /**
    * Adds a line break to the given {@link StringBuffer}.
    * @param sb The {@link StringBuffer} to write to.
    */
   protected void appendNewLine(StringBuffer sb) {
      sb.append(StringUtil.NEW_LINE);
   }
}
