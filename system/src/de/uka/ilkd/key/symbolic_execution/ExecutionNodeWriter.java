// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.Map;

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
import de.uka.ilkd.key.symbolic_execution.model.IExecutionUseLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionUseOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Allows to persistent selected properties of {@link IExecutionNode}s
 * as XML file. Such files can be read via an {@link ExecutionNodeReader} instance.
 * @author Martin Hentschel
 * @see ExecutionNodeReader
 */
public class ExecutionNodeWriter extends AbstractWriter {   
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
    * Attribute name to store {@link IExecutionValue#getConditionString()}.
    */
   public static final String ATTRIBUTE_CONDITION_STRING = "conditionString";

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
    * Attribute name to store {@link IExecutionBranchCondition#isMergedBranchCondition()}.
    */
   public static final String ATTRIBUTE_MERGED_BRANCH_CONDITION = "mergedBranchCondition";

   /**
    * Attribute name to store {@link IExecutionVariable#isValueAnObject()}.
    */
   public static final String ATTRIBUTE_IS_VALUE_AN_OBJECT = "isValueAnObject";

   /**
    * Attribute name to store {@link IExecutionVariable#isValueUnknown()}.
    */
   public static final String ATTRIBUTE_IS_VALUE_UNKNOWN = "isValueUnknown";

   /**
    * Attribute name to store {@link IExecutionUseOperationContract#isPreconditionComplied()}.
    */
   public static final String ATTRIBUTE_PRECONDITION_COMPLIED = "preconditionComplied";

   /**
    * Attribute name to store {@link IExecutionUseOperationContract#hasNotNullCheck()}.
    */
   public static final String ATTRIBUTE_HAS_NOT_NULL_CHECK = "hasNotNullCheck";

   /**
    * Attribute name to store {@link IExecutionMethodReturn#isReturnValueComputed()}.
    */
   public static final String ATTRIBUTE_RETURN_VALUE_COMPUTED = "isReturnValueComputed";

   /**
    * Attribute name to store {@link IExecutionBranchCondition#isBranchConditionComputed()}.
    */
   public static final String ATTRIBUTE_BRANCH_CONDITION_COMPUTED = "isBranchConditionComputed";
   
   /**
    * Attribute name to store {@link IExecutionUseOperationContract#isNotNullCheckComplied()}.
    */
   public static final String ATTRIBUTE_NOT_NULL_CHECK_COMPLIED = "notNullCheckComplied";

   /**
    * Attribute name to store {@link IExecutionUseLoopInvariant#isInitiallyValid()}.
    */
   public static final String ATTRIBUTE_INITIALLY_VALID = "initiallyValid";
   
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
    * Tag name to store {@link IExecutionUseOperationContract}s.
    */
   public static final String TAG_USE_OPERATION_CONTRACT = "useOperationContract";

   /**
    * Tag name to store {@link IExecutionUseLoopInvariant}s.
    */
   public static final String TAG_USE_LOOP_INVARIANT = "useLoopInvariant";

   /**
    * Tag name to store {@link IExecutionVariable}s.
    */
   public static final String TAG_VARIABLE = "variable";

   /**
    * Tag name to store {@link IExecutionValue}s.
    */
   public static final String TAG_VALUE = "value";

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
      else if (node instanceof IExecutionUseOperationContract) {
         appendExecutionUseOperationContract(level, (IExecutionUseOperationContract)node, saveVariables, saveCallStack, sb);
      }
      else if (node instanceof IExecutionUseLoopInvariant) {
         appendExecutionUseLoopInvariant(level, (IExecutionUseLoopInvariant)node, saveVariables, saveCallStack, sb);
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
      attributeValues.put(ATTRIBUTE_MERGED_BRANCH_CONDITION, node.isMergedBranchCondition() + "");
      attributeValues.put(ATTRIBUTE_BRANCH_CONDITION_COMPUTED, node.isBranchConditionComputed() + "");
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
      attributeValues.put(ATTRIBUTE_RETURN_VALUE_COMPUTED, node.isReturnValueComputed() + "");
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
    * Converts the given {@link IExecutionUseOperationContract} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionUseOperationContract} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionUseOperationContract(int level, 
                                                     IExecutionUseOperationContract node, 
                                                     boolean saveVariables, 
                                                     boolean saveCallStack, 
                                                     StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");

      attributeValues.put(ATTRIBUTE_PRECONDITION_COMPLIED, node.isPreconditionComplied() + "");
      attributeValues.put(ATTRIBUTE_HAS_NOT_NULL_CHECK, node.hasNotNullCheck() + "");
      attributeValues.put(ATTRIBUTE_NOT_NULL_CHECK_COMPLIED, node.isNotNullCheckComplied() + "");
      
      appendStartTag(level, TAG_USE_OPERATION_CONTRACT, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_USE_OPERATION_CONTRACT, sb);
   }

   /**
    * Converts the given {@link IExecutionUseLoopInvariant} into XML and appends it to the {@link StringBuffer}.
    * @param level The current child level.
    * @param node The {@link IExecutionUseLoopInvariant} to convert.
    * @param saveVariables Save variables? 
    * @param saveCallStack Save method call stack?
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendExecutionUseLoopInvariant(int level, 
                                         IExecutionUseLoopInvariant node, 
                                         boolean saveVariables, 
                                         boolean saveCallStack, 
                                         StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, node.getName());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION, node.getFormatedPathCondition());
      attributeValues.put(ATTRIBUTE_PATH_CONDITION_CHANGED, node.isPathConditionChanged() + "");

      attributeValues.put(ATTRIBUTE_INITIALLY_VALID, node.isInitiallyValid() + "");

      appendStartTag(level, TAG_USE_LOOP_INVARIANT, attributeValues, sb);
      appendVariables(level + 1, node, saveVariables, sb);
      appendCallStack(level + 1, node, saveCallStack, sb);
      appendChildren(level + 1, node, saveVariables, saveCallStack, sb);
      appendEndTag(level, TAG_USE_LOOP_INVARIANT, sb);
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
      attributeValues.put(ATTRIBUTE_ARRAY_INDEX, variable.getArrayIndex() + "");
      attributeValues.put(ATTRIBUTE_IS_ARRAY_INDEX, variable.isArrayIndex() + "");
      appendStartTag(level, TAG_VARIABLE, attributeValues, sb);
      appendValues(level + 1, variable, sb);
      appendEndTag(level, TAG_VARIABLE, sb);
   }

   /**
    * Appends the contained {@link IExecutionValue}s to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param variable The {@link IExecutionVariable} which provides the {@link IExecutionValue}s.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendValues(int level, IExecutionVariable variable, StringBuffer sb) throws ProofInputException {
      IExecutionValue[] values = variable.getValues();
      for (IExecutionValue value : values) {
         appendValue(level, value, sb);
      }
   }

   /**
    * Appends the given {@link IExecutionValue} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param value The {@link IExecutionValue} to append.
    * @param sb The {@link StringBuffer} to append to.
    * @throws ProofInputException Occurred Exception.
    */
   protected void appendValue(int level, IExecutionValue value, StringBuffer sb) throws ProofInputException {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, value.getName());
      attributeValues.put(ATTRIBUTE_TYPE_STRING, value.getTypeString());
      attributeValues.put(ATTRIBUTE_VALUE_STRING, value.getValueString());
      attributeValues.put(ATTRIBUTE_IS_VALUE_AN_OBJECT, value.isValueAnObject() + "");
      attributeValues.put(ATTRIBUTE_IS_VALUE_UNKNOWN, value.isValueUnknown() + "");
      attributeValues.put(ATTRIBUTE_CONDITION_STRING, value.getConditionString());
      appendStartTag(level, TAG_VALUE, attributeValues, sb);

      IExecutionVariable[] childVariables = value.getChildVariables();
      for (IExecutionVariable childVariable : childVariables) {
         appendVariable(level + 1, childVariable, sb);
      }
      appendEndTag(level, TAG_VALUE, sb);
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
}