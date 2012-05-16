package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.Charset;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Allows to persistent selected properties of {@link IExecutionNode}s
 * as XML file. Such files can be read via an {@link ExecutionNodeReader} instance.
 * @author Martin Hentschel
 * @see ExecutionNodeReader
 */
public class ExecutionNodeWriter {
   /**
    * New line.
    */
   public static final String NEW_LINE = System.getProperty("line.separator");
   
   /**
    * The used leading white space in each level.
    */
   public static final String LEADING_WHITE_SPACE_PER_LEVEL = "   ";
   
   /**
    * Attribute name to store encodings.
    */
   public static final String ATTRIBUTE_ENCODING = "encoding";
   
   /**
    * Attribute name to store {@link IExecutionNode#getName()}.
    */
   public static final String ATTRIBUTE_NAME = "name";

   /**
    * Attribute name to store {@link IExecutionMethodReturn#getNameIncludingReturnValue()}.
    */
   public static final String ATTRIBUTE_NAME_INCLUDING_RETURN_VALUE = "nameIncludingReturnValue";

   /**
    * Attribute exceptional termination to store {@link IExecutionTermination#isExceptionalTermination()}.
    */
   public static final String ATTRIBUTE_EXCEPTIONAL_TERMINATION = "exceptionalTermination";
   
   /**
    * The default enconding.
    */
   public static final String DEFAULT_ENCODING = "UTF-8";
   
   /**
    * Tag name to store {@link IExecutionBranchCondition}s.
    */
   public static final String TAG_BRANCH_CONDITION = "branchCondition";

   /**
    * Tag name to store {@link IExecutionStartNode}s.
    */
   public static final String TAG_START_NODE = "startNode";

   /**
    * Tag name to store {@link IExecutionBranchNode}s.
    */
   public static final String TAG_BRANCH_NODE = "branchNode";

   /**
    * Tag name to store {@link IExecutionLoopCondition}s.
    */
   public static final String TAG_LOOP_CONDITION = "loopCondition";

   /**
    * Tag name to store {@link IExecutionLoopNode}s.
    */
   public static final String TAG_LOOP_NODE = "loopNode";

   /**
    * Tag name to store {@link IExecutionMethodCall}s.
    */
   public static final String TAG_METHOD_CALL = "methodCall";

   /**
    * Tag name to store {@link IExecutionMethodReturn}s.
    */
   public static final String TAG_METHOD_RETURN = "methodReturn";

   /**
    * Tag name to store {@link IExecutionStatement}s.
    */
   public static final String TAG_STATEMENT = "statement";

   /**
    * Tag name to store {@link IExecutionTermination}s.
    */
   public static final String TAG_TERMINATION = "termination";

   /**
    * Writes the given {@link IExecutionNode} as XML file.
    * @param node The {@link IExecutionNode} to save.
    * @param encoding The encoding to use.
    * @param file The {@link File} to save to.
    * @throws IOException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public void write(IExecutionNode node, String encoding, File file) throws IOException, ProofInputException {
      write(node, encoding, new FileOutputStream(file));
   }
   
   /**
    * Writes the given {@link IExecutionNode} into the {@link OutputStream}.
    * @param node The {@link IExecutionNode} to save.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to save to. The {@link OutputStream} will be closed by this method. 
    * @throws IOException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public void write(IExecutionNode node, String encoding, OutputStream out) throws IOException, ProofInputException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(node, charset.displayName());
            out.write(xml.getBytes(charset));
         }
         finally {
            out.close();
         }
      }
   }
   
   /**
    * Converts the given {@link IExecutionNode} into XML.
    * @param node The {@link IExecutionNode} to convert.
    * @param encoding The encoding to use.
    * @return The craeted XML content.
    * @throws ProofInputException Occurred Exception.
    */
   public String toXML(IExecutionNode node, String encoding) throws ProofInputException {
      StringBuffer sb = new StringBuffer();
      appendXmlHeader(encoding, sb);
      appendExecutionNode(0, node, sb);
      return sb.toString();
   }
   
   /**
    * Converts the given {@link IExecutionNode} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionNode} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionNode(int level, IExecutionNode node, StringBuffer sb) throws ProofInputException {
      if (node instanceof IExecutionBranchCondition) {
         appendExecutionBranchCondition(level, (IExecutionBranchCondition)node, sb);
      }
      else if (node instanceof IExecutionStartNode) {
         appendExecutionStartNode(level, (IExecutionStartNode)node, sb);
      }
      else if (node instanceof IExecutionBranchNode) {
         appendExecutionBranchNode(level, (IExecutionBranchNode)node, sb);
      }
      else if (node instanceof IExecutionLoopCondition) {
         appendExecutionLoopCondition(level, (IExecutionLoopCondition)node, sb);
      }
      else if (node instanceof IExecutionLoopNode) {
         appendExecutionLoopNode(level, (IExecutionLoopNode)node, sb);
      }
      else if (node instanceof IExecutionMethodCall) {
         appendExecutionMethodCall(level, (IExecutionMethodCall)node, sb);
      }
      else if (node instanceof IExecutionMethodReturn) {
         appendExecutionMethodReturn(level, (IExecutionMethodReturn)node, sb);
      }
      else if (node instanceof IExecutionStatement) {
         appendExecutionStatement(level, (IExecutionStatement)node, sb);
      }
      else if (node instanceof IExecutionTermination) {
         appendExecutionTermination(level, (IExecutionTermination)node, sb);
      }
      else {
         throw new IllegalArgumentException("Not supported node \"" + node + "\".");
      }
   }

   /**
    * Converts the given {@link IExecutionBranchCondition} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionBranchCondition} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionBranchCondition(int level, IExecutionBranchCondition node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      appendStartTag(level, TAG_BRANCH_CONDITION, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_BRANCH_CONDITION, sb);
   }

   /**
    * Converts the given {@link IExecutionStartNode} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionStartNode} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionStartNode(int level, IExecutionStartNode node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      appendStartTag(level, TAG_START_NODE, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_START_NODE, sb);
   }

   /**
    * Converts the given {@link IExecutionLoopCondition} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionLoopCondition} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionBranchNode(int level, IExecutionBranchNode node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      appendStartTag(level, TAG_BRANCH_NODE, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_BRANCH_NODE, sb);
   }

   /**
    * Converts the given {@link IExecutionLoopCondition} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionLoopCondition} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionLoopCondition(int level, IExecutionLoopCondition node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      appendStartTag(level, TAG_LOOP_CONDITION, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_LOOP_CONDITION, sb);
   }

   /**
    * Converts the given {@link IExecutionLoopNode} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionLoopNode} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionLoopNode(int level, IExecutionLoopNode node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      appendStartTag(level, TAG_LOOP_NODE, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_LOOP_NODE, sb);
   }

   /**
    * Converts the given {@link IExecutionMethodCall} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionMethodCall} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionMethodCall(int level, IExecutionMethodCall node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      appendStartTag(level, TAG_METHOD_CALL, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_METHOD_CALL, sb);
   }

   /**
    * Converts the given {@link IExecutionMethodReturn} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionMethodReturn} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionMethodReturn(int level, IExecutionMethodReturn node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_NAME_INCLUDING_RETURN_VALUE, node.getNameIncludingReturnValue());
      appendStartTag(level, TAG_METHOD_RETURN, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_METHOD_RETURN, sb);
   }

   /**
    * Converts the given {@link IExecutionStatement} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionStatement} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionStatement(int level, IExecutionStatement node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      appendStartTag(level, TAG_STATEMENT, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_STATEMENT, sb);
   }

   /**
    * Converts the given {@link IExecutionTermination} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionTermination} to convert.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionTermination(int level, IExecutionTermination node, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_EXCEPTIONAL_TERMINATION, Boolean.valueOf(node.isExceptionalTermination()).toString());
      appendStartTag(level, TAG_TERMINATION, attributeValues, sb);
      appendChildren(level + 1, node, sb);
      appendEndTag(level, TAG_TERMINATION, sb);
   }

   /**
    * Appends the child nodes to the given {@link StringBuffer}.
    * @param childLevel The level of the children.
    * @param parent The parent {@link IExecutionNode} which provides the children.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendChildren(int childLevel, IExecutionNode parent, StringBuffer sb) throws ProofInputException {
      IExecutionNode[] children = parent.getChildren();
      for (IExecutionNode child : children) {
         appendExecutionNode(childLevel, child, sb);
      }
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
         sb.append(JavaUtil.encodeText(value));
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
      sb.append(NEW_LINE);
   }
}
