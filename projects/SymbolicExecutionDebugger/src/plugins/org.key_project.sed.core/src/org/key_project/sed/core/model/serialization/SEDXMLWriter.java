package org.key_project.sed.core.model.serialization;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
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
    * Tag name to store {@link ISEDBranchNode}s.
    */
   public static final String TAG_BRANCH_NODE = "sedBranchNode";

   /**
    * Tag name to store {@link ISEDExceptionalTermination}s.
    */
   public static final String TAG_EXCEPTIONAL_TERMINATION = "sedExceptionalTermination";

   /**
    * Tag name to store {@link ISEDLoopCondition}s.
    */
   public static final String TAG_LOOP_CONDITION = "sedLoopCondition";

   /**
    * Tag name to store {@link ISEDLoopNode}s.
    */
   public static final String TAG_LOOP_NODE = "sedLoopNode";

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
    * Writes the given {@link ISEDDebugTarget}s into the {@link OutputStream} with the defined encoding.
    * @param targets The {@link ISEDDebugTarget}s to write.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to use.
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, String encoding, OutputStream out) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName());
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
    * @throws DebugException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public void write(ILaunch launch, String encoding, OutputStream out) throws DebugException, IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName());
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
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(ILaunch launch, String encoding, IFile file) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(launch, charset.displayName());
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
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public void write(IDebugTarget[] targets, String encoding, IFile file) throws IOException, CoreException {
      if (file != null) {
         InputStream in = null;
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(targets, charset.displayName());
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
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(ILaunch launch, String encoding) throws DebugException {
      StringBuffer sb = new StringBuffer();
      if (launch != null) {
         sb.append(toXML(launch.getDebugTargets(), encoding));
      }
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link IDebugTarget}s into a {@link String} with the given encoding.
    * @param launch The {@link ILaunch} to serialize.
    * @param encoding The encoding to use.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   public String toXML(IDebugTarget[] targets, String encoding) throws DebugException {
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
               sb.append(toXML(1, (ISEDDebugTarget)target));
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
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDDebugTarget target) throws DebugException {
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
            sb.append(toXML(level + 1, thread));
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
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDDebugNode node) throws DebugException {
      if (node instanceof ISEDBranchCondition) {
         return toXML(level, (ISEDBranchCondition)node);
      }
      else if (node instanceof ISEDBranchNode) {
         return toXML(level, (ISEDBranchNode)node);
      }
      else if (node instanceof ISEDExceptionalTermination) {
         return toXML(level, (ISEDExceptionalTermination)node);
      }
      else if (node instanceof ISEDLoopCondition) {
         return toXML(level, (ISEDLoopCondition)node);
      }
      else if (node instanceof ISEDLoopNode) {
         return toXML(level, (ISEDLoopNode)node);
      }
      else if (node instanceof ISEDMethodCall) {
         return toXML(level, (ISEDMethodCall)node);
      }
      else if (node instanceof ISEDMethodReturn) {
         return toXML(level, (ISEDMethodReturn)node);
      }
      else if (node instanceof ISEDStatement) {
         return toXML(level, (ISEDStatement)node);
      }
      else if (node instanceof ISEDTermination) {
         return toXML(level, (ISEDTermination)node);
      }
      else if (node instanceof ISEDThread) {
         return toXML(level, (ISEDThread)node);
      }
      else {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Unknown node type of node \"" + node + "\"."));
      }
   }
   
   /**
    * Serializes the given {@link ISEDBranchCondition} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDBranchCondition} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDBranchCondition branchCondition) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_CONDITION, branchCondition, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDBranchNode} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDBranchNode} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDBranchNode branchNode) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_BRANCH_NODE, branchNode, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDExceptionalTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDExceptionalTermination} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDExceptionalTermination exceptionalTermination) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_EXCEPTIONAL_TERMINATION, exceptionalTermination, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopCondition} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDLoopCondition} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDLoopCondition loopCondition) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_CONDITION, loopCondition, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDLoopNode} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDLoopNode} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDLoopNode loopNode) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_LOOP_NODE, loopNode, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDMethodCall} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDMethodCall} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDMethodCall methodCall) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_CALL, methodCall, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDMethodReturn} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDMethodReturn} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDMethodReturn methodReturn) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_METHOD_RETURN, methodReturn, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDStatement} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDStatement} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDStatement statement) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_STATEMENT, statement, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDTermination} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDTermination} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDTermination termination) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_TERMINATION, termination, sb);
      return sb.toString();
   }
   
   /**
    * Serializes the given {@link ISEDThread} into a {@link String}.
    * @param level The level in the tree used for leading white space (formating).
    * @param target The {@link ISEDThread} to serialize.
    * @return The serialized {@link String}.
    * @throws DebugException Occurred Exception.
    */
   protected String toXML(int level, ISEDThread thread) throws DebugException {
      StringBuffer sb = new StringBuffer();
      appendNode(level, TAG_THREAD, thread, sb);
      return sb.toString();
   }
   
   /**
    * Adds an {@link ISEDDebugNode} to the given {@link StringBuffer}.
    * @param level The level in the tree used for leading white space (formating).
    * @param tagName The tag name to use.
    * @param node The {@link ISEDDebugNode} to serialize.
    * @param sb The {@link StringBuffer} to write to.
    * @throws DebugException Occurred Exception.
    */
   protected void appendNode(int level, String tagName, ISEDDebugNode node, StringBuffer sb) throws DebugException {
      if (node != null) {
         appendWhiteSpace(level, sb);
         sb.append("<");
         sb.append(tagName);
         appendAttribute(ATTRIBUTE_ID, node.getId(), sb);
         appendAttribute(ATTRIBUTE_NAME, node.getName(), sb);
         if (node instanceof IStackFrame) {
            IStackFrame frame = (IStackFrame)node;
            appendAttribute(ATTRIBUTE_LINE_NUMBER, frame.getLineNumber(), sb);
            appendAttribute(ATTRIBUTE_CHAR_START, frame.getCharStart(), sb);
            appendAttribute(ATTRIBUTE_CHAR_END, frame.getCharEnd(), sb);
         }
         sb.append(">");
         appendNewLine(sb);
         ISEDDebugNode[] children = node.getChildren();
         for (ISEDDebugNode child : children) {
            sb.append(toXML(level + 1, child));
         }
         appendWhiteSpace(level, sb);
         sb.append("</");
         sb.append(tagName);
         sb.append(">");
         appendNewLine(sb);
      }
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
   protected void appendAttribute(String attributeName, int value, StringBuffer sb) {
      sb.append(" ");
      sb.append(attributeName);
      sb.append("=\"");
      sb.append(value);
      sb.append("\"");
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
