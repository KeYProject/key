package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
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
    * Attribute name to store {@link IExecutionElement#getName()}.
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
    * Attribute name to store {@link IExecutionVariable#getTypeString()}.
    */
   public static final String ATTRIBUTE_TYPE_STRING = "typeString";

   /**
    * Attribute name to store {@link IExecutionVariable#getValueString()}.
    */
   public static final String ATTRIBUTE_VALUE_STRING = "valueString";

   /**
    * Attribute name to store {@link IExecutionVariable#getArrayIndex()}.
    */
   public static final String ATTRIBUTE_ARRAY_INDEX = "arrayIndex";

   /**
    * Attribute name to store {@link IExecutionVariable#isArrayIndex()}.
    */
   public static final String ATTRIBUTE_IS_ARRAY_INDEX = "isArrayIndex";

   /**
    * Attribute name to store {@link IExecutionBranchCondition#getFormatedBranchCondition()}.
    */
   public static final String ATTRIBUTE_BRANCH_CONDITION = "branchCondition";

   /**
    * Attribute name to store {@link IExecutionNode#getPathCondition()}.
    */
   public static final String ATTRIBUTE_PATH_CONDITION = "pathCondition";

   /**
    * Attribute name to store {@link IExecutionNode#isPathConditionChanged()}.
    */
   public static final String ATTRIBUTE_PATH_CONDITION_CHANGED = "pathConditionChanged";

   /**
    * A path which refers to an {@link IExecutionNode} starting from the root.
    */
   public static final String ATTRIBUTE_PATH_IN_TREE = "path";
   
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
    * Tag name to store {@link IExecutionVariable}s.
    */
   public static final String TAG_VARIABLE = "variable";

   /**
    * Tag name to store one entry of {@link IExecutionNode#getCallStack()}.
    */
   public static final String TAG_CALL_STACK_ENTRY = "callStackEntry";

   /**
    * Character to separate path entries in attributes {@value #ATTRIBUTE_PATH_IN_TREE}.
    */
   public static final char PATH_SEPARATOR = '/';

   /**
    * Writes the given {@link IExecutionNode} as XML file.
    * @param node The {@link IExecutionNode} to save.
    * @param encoding The encoding to use.
    * @param file The {@link File} to save to.
    * @param saveVariables Save variables?
    * @param saveCallStack Save method call stack?
    * @throws IOException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public void write(IExecutionNode node, 
                     String encoding, 
                     File file, 
                     boolean saveVariables,
                     boolean saveCallStack) throws IOException, ProofInputException {
      write(node, encoding, new FileOutputStream(file), saveVariables, saveCallStack);
   }
   
   /**
    * Writes the given {@link IExecutionNode} into the {@link OutputStream}.
    * @param node The {@link IExecutionNode} to save.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to save to. The {@link OutputStream} will be closed by this method.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @throws IOException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public void write(IExecutionNode node, 
                     String encoding, 
                     OutputStream out, 
                     boolean saveVariables,
                     boolean saveCallStack) throws IOException, ProofInputException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(node, charset.displayName(), saveVariables, saveCallStack);
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
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @return The created XML content.
    * @throws ProofInputException Occurred Exception.
    */
   public String toXML(IExecutionNode node, 
                       String encoding, 
                       boolean saveVariables,
                       boolean saveCallStack) throws ProofInputException {
      StringBuffer sb = new StringBuffer();
      appendXmlHeader(encoding, sb);
      appendExecutionNode(0, node, saveVariables, saveCallStack, sb);
      return sb.toString();
   }
   
   /**
    * Converts the given {@link IExecutionNode} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionNode} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionNode(int level, 
                                      IExecutionNode node, 
                                      boolean saveVariables, 
                                      boolean saveCallStack,
                                      StringBuffer sb) throws ProofInputException {
      if (node instanceof IExecutionBranchCondition) {
         appendExecutionBranchCondition(level, (IExecutionBranchCondition)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionStartNode) {
         appendExecutionStartNode(level, (IExecutionStartNode)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionBranchNode) {
         appendExecutionBranchNode(level, (IExecutionBranchNode)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionLoopCondition) {
         appendExecutionLoopCondition(level, (IExecutionLoopCondition)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionLoopNode) {
         appendExecutionLoopNode(level, (IExecutionLoopNode)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionMethodCall) {
         appendExecutionMethodCall(level, (IExecutionMethodCall)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionMethodReturn) {
         appendExecutionMethodReturn(level, (IExecutionMethodReturn)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionStatement) {
         appendExecutionStatement(level, (IExecutionStatement)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionTermination) {
         appendExecutionTermination(level, (IExecutionTermination)node, saveVariables, saveCallStack, sb);
      }
      else {
         throw new IllegalArgumentException("Not supported node \"" + node + "\".");
      }
   }

   /**
    * Converts the given {@link IExecutionBranchCondition} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionBranchCondition} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionBranchCondition(int level, 
                                                 IExecutionBranchCondition node, 
                                                 boolean saveVariables, 
                                                 boolean saveCallStack, 
                                                 StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      attributeValues.put(ATTRIBUTE_BRANCH_CONDITION, node.getFormatedBranchCondition());
      appendStartTag(level, TAG_BRANCH_CONDITION, attributeValues, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_BRANCH_CONDITION, sb);
   }

   /**
    * Converts the given {@link IExecutionStartNode} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionStartNode} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionStartNode(int level, 
                                           IExecutionStartNode node, 
                                           boolean saveVariables, 
                                           boolean saveCallStack,
                                           StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      appendStartTag(level, TAG_START_NODE, attributeValues, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_START_NODE, sb);
   }

   /**
    * Converts the given {@link IExecutionLoopCondition} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionLoopCondition} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionBranchNode(int level, 
                                            IExecutionBranchNode node, 
                                            boolean saveVariables, 
                                            boolean saveCallStack, 
                                            StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      appendStartTag(level, TAG_BRANCH_NODE, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_BRANCH_NODE, sb);
   }

   /**
    * Converts the given {@link IExecutionLoopCondition} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionLoopCondition} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionLoopCondition(int level, 
                                               IExecutionLoopCondition node, 
                                               boolean saveVariables, 
                                               boolean saveCallStack, 
                                               StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      appendStartTag(level, TAG_LOOP_CONDITION, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_LOOP_CONDITION, sb);
   }

   /**
    * Converts the given {@link IExecutionLoopNode} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionLoopNode} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionLoopNode(int level, 
                                          IExecutionLoopNode node, 
                                          boolean saveVariables, 
                                          boolean saveCallStack,
                                          StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      appendStartTag(level, TAG_LOOP_NODE, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_LOOP_NODE, sb);
   }

   /**
    * Converts the given {@link IExecutionMethodCall} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionMethodCall} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionMethodCall(int level, 
                                            IExecutionMethodCall node, 
                                            boolean saveVariables, 
                                            boolean saveCallStack,
                                            StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      appendStartTag(level, TAG_METHOD_CALL, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_METHOD_CALL, sb);
   }

   /**
    * Converts the given {@link IExecutionMethodReturn} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionMethodReturn} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionMethodReturn(int level, 
                                              IExecutionMethodReturn node, 
                                              boolean saveVariables,
                                              boolean saveCallStack, 
                                              StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      attributeValues.put(ATTRIBUTE_NAME_INCLUDING_RETURN_VALUE, node.getNameIncludingReturnValue());
      appendStartTag(level, TAG_METHOD_RETURN, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_METHOD_RETURN, sb);
   }

   /**
    * Converts the given {@link IExecutionStatement} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionStatement} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionStatement(int level, 
                                           IExecutionStatement node, 
                                           boolean saveVariables, 
                                           boolean saveCallStack, 
                                           StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      appendStartTag(level, TAG_STATEMENT, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_STATEMENT, sb);
   }

   /**
    * Converts the given {@link IExecutionTermination} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionTermination} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionTermination(int level, 
                                             IExecutionTermination node, 
                                             boolean saveVariables,
                                             boolean saveCallStack,
                                             StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");
      attributeValues.put(ATTRIBUTE_EXCEPTIONAL_TERMINATION, Boolean.valueOf(node.isExceptionalTermination()).toString());
      appendStartTag(level, TAG_TERMINATION, attributeValues, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_TERMINATION, sb);
   }

   /**
    * Appends the contained {@link IExecutionVariable}s to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param node The {@link IExecutionStateNode} which provides the {@link IExecutionVariable}s.
    * @param saveVariables Save variables? 
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendVariables(int level, IExecutionStateNode<?> node, boolean saveVariables, StringBuffer sb) throws ProofInputException {
      if (saveVariables) {
         IExecutionVariable[] variables = node.getVariables();
         for (IExecutionVariable variable : variables) {
            appendVariable(level, variable, sb);
         }
      }
   }

   /**
    * Appends the given {@link IExecutionVariable} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param variable The {@link IExecutionVariable} to append.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendVariable(int level, IExecutionVariable variable, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, variable.getName());
      attributeValues.put(ATTRIBUTE_TYPE_STRING, variable.getTypeString());
      attributeValues.put(ATTRIBUTE_VALUE_STRING, variable.getValueString());
      attributeValues.put(ATTRIBUTE_ARRAY_INDEX, variable.getArrayIndex() + "");
      attributeValues.put(ATTRIBUTE_IS_ARRAY_INDEX, variable.isArrayIndex() + "");
      appendStartTag(level, TAG_VARIABLE, attributeValues, sb);

      IExecutionVariable[] childVariables = variable.getChildVariables();
      for (IExecutionVariable childVariable : childVariables) {
         appendVariable(level + 1, childVariable, sb);
      }
      appendEndTag(level, TAG_VARIABLE, sb);
   }

   /**
    * Appends the child nodes to the given {@link StringBuffer}.
    * @param childLevel The level of the children.
    * @param parent The parent {@link IExecutionNode} which provides the children.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendChildren(int childLevel, 
                                 IExecutionNode parent, 
                                 boolean saveVariables, 
                                 boolean saveCallStack,
                                 StringBuffer sb) throws ProofInputException {
      IExecutionNode[] children = parent.getChildren();
      for (IExecutionNode child : children) {
         appendExecutionNode(childLevel, child, saveVariables, saveCallStack, sb);
      }
   }

   /**
    * Appends the call stack entries if required to the given {@link StringBuffer}.
    * @param level The level of the children.
    * @param node The {@link IExecutionNode} which provides the call stack.
    * @param saveCallStack Defines if the call stack should be saved or not.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendCallStack(int level, IExecutionNode node, boolean saveCallStack, StringBuffer sb) {
      if (saveCallStack) {
         IExecutionNode[] callStack = node.getCallStack();
         if (callStack != null) {
            for (IExecutionNode stackNode : callStack) {
               Map<String, String> attributeValues = new LinkedHashMap<String, String>();
               attributeValues.put(ATTRIBUTE_PATH_IN_TREE, computePath(stackNode));
               appendEmptyTag(level, TAG_CALL_STACK_ENTRY, attributeValues, sb);
            }
         }
      }
   }

   /**
    * Computes the path from the root of the symbolic execution tree to the given {@link IExecutionNode}.
    * @param node The {@link IExecutionNode} to compute path to.
    * @return The computed path.
    */
   protected String computePath(IExecutionNode node) {
      StringBuffer sb = new StringBuffer();
      boolean afterFirst = false;
      while (node != null) {
         IExecutionNode parent = node.getParent();
         if (parent != null) {
            if (afterFirst) {
               sb.insert(0, PATH_SEPARATOR);
            }
            else {
               afterFirst = true;
            }
            int index = JavaUtil.indexOf(parent.getChildren(), node);
            assert index >= 0 : "Node \"" + node + "\" is not contained in parents children \"" + Arrays.toString(parent.getChildren()) + "\".";
            sb.insert(0, index);
         }
         else {
            sb.insert(0, PATH_SEPARATOR);
         }
         node = parent;
      }
      return sb.toString();
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
