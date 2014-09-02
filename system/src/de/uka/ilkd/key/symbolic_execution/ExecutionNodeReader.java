// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.StringTokenizer;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionExceptionalMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;

/**
 * Allows to read XML files which contains an symbolic execution tree
 * written via an {@link ExecutionNodeWriter}.
 * @author Martin Hentschel
 * @see ExecutionNodeWriter
 */
public class ExecutionNodeReader {
   /**
    * Reads the given {@link File}.
    * @param file The {@link File} to read.
    * @return The root of the read symbolic execution tree.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public IExecutionNode read(File file) throws ParserConfigurationException, SAXException, IOException {
      return read(new FileInputStream(file));
   }
   
   /**
    * Reads from the given {@link InputStream} and closes it.
    * @param in The {@link InputStream} to read from.
    * @return The root of the read symbolic execution tree.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public IExecutionNode read(InputStream in) throws ParserConfigurationException, SAXException, IOException {
      if (in != null) {
         try {
            // Parse XML file
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setNamespaceAware(true);
            SAXParser saxParser = factory.newSAXParser();
            SEDSAXHandler handler = new SEDSAXHandler();
            saxParser.parse(in, handler);
            // Get root 
            IExecutionNode root = handler.getRoot();
            // Construct call stacks
            Set<Entry<AbstractKeYlessExecutionNode, List<String>>> entries = handler.getCallStackPathEntries().entrySet();
            for (Entry<AbstractKeYlessExecutionNode, List<String>> entry : entries) {
               for (String path : entry.getValue()) {
                  IExecutionNode stackEntry = findNode(root, path);
                  if (stackEntry == null) {
                     throw new SAXException("Can't find call stack entry \"" + path + "\" in parsed symbolic execution tree.");
                  }
                  entry.getKey().addCallStackEntry(stackEntry);
               }
            }
            // Construct method returns
            Set<Entry<KeYlessMethodCall, List<String>>> methodReturnEntries = handler.getMethodReturnPathEntries().entrySet();
            for (Entry<KeYlessMethodCall, List<String>> entry : methodReturnEntries) {
               for (String path : entry.getValue()) {
                  IExecutionNode returnEntry = findNode(root, path);
                  if (returnEntry == null) {
                     throw new SAXException("Can't find method return entry \"" + path + "\" in parsed symbolic execution tree.");
                  }
                  if (!(returnEntry instanceof IExecutionBaseMethodReturn<?>)) {
                     throw new SAXException("Expected basemethod return on \"" + path + "\" but is " + returnEntry.getElementType() + ".");
                  }
                  entry.getKey().addMethodReturn((IExecutionBaseMethodReturn<?>)returnEntry);
               }
            }
            // Construct terminations
            Set<Entry<KeYlessStart, List<String>>> terminationEntries = handler.getTerminationPathEntries().entrySet();
            for (Entry<KeYlessStart, List<String>> entry : terminationEntries) {
               for (String path : entry.getValue()) {
                  IExecutionNode terminationEntry = findNode(root, path);
                  if (terminationEntry == null) {
                     throw new SAXException("Can't find termination entry \"" + path + "\" in parsed symbolic execution tree.");
                  }
                  if (!(terminationEntry instanceof IExecutionTermination)) {
                     throw new SAXException("Expected termination on \"" + path + "\" but is " + terminationEntry.getElementType() + ".");
                  }
                  entry.getKey().addTermination((IExecutionTermination)terminationEntry);
               }
            }
            // Return result
            return root;
         }
         finally {
            in.close();
         }
      }
      else {
         return null;
      }
   }

   /**
    * Searches the {@link IExecutionNode} starting at the given root
    * which is defined by the path.
    * @param root The {@link IExecutionNode} to start search.
    * @param path The path.
    * @return The found {@link IExecutionNode}.
    * @throws SAXException If it was not possible to find the node.
    */
   protected IExecutionNode findNode(IExecutionNode root, String path) throws SAXException {
      if (path != null && !path.isEmpty()) {
         StringTokenizer tokenizer = new StringTokenizer(path, ExecutionNodeWriter.PATH_SEPARATOR + "");
         while (tokenizer.hasMoreTokens()) {
            String next = tokenizer.nextToken();
            try {
               int childIndex = Integer.parseInt(next);
               if (childIndex < 0) {
                  throw new SAXException("Path segment \"" + next + "\" of path \"" + path + "\" is a negative integer.");
               }
               IExecutionNode[] children = root.getChildren();
               if (childIndex >= children.length) {
                  throw new SAXException("Path segment \"" + next + "\" of path \"" + path + "\" is outside of the child array range.");
               }
               root = children[childIndex];
            }
            catch (NumberFormatException e) {
               throw new SAXException("Path segment \"" + next + "\" of path \"" + path + "\" is no valid integer.", e);
            }
         }
      }
      return root;
   }

   /**
    * {@link DefaultHandler} implementation used in {@link ExecutionNodeReader#read(InputStream)}.
    * @author Martin Hentschel
    */
   private class SEDSAXHandler extends DefaultHandler {
      /**
       * The root of the read symbolic execution tree.
       */
      private IExecutionNode root;

      /**
       * The parent hierarchy filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private final Deque<AbstractKeYlessExecutionNode> parentNodeStack = new LinkedList<AbstractKeYlessExecutionNode>();

      /**
       * The parent hierarchy of {@link IExecutionVariable} and {@link IExecutionValue} filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}. 
       */
      private final Deque<Object> parentVariableValueStack = new LinkedList<Object>();
      
      /**
       * Maps an {@link AbstractKeYlessExecutionNode} to the path entries of its call stack.
       */
      private final Map<AbstractKeYlessExecutionNode, List<String>> callStackPathEntries = new LinkedHashMap<AbstractKeYlessExecutionNode, List<String>>();
      
      /**
       * Maps an {@link KeYlessMethodCall} to the path entries of its method returns.
       */
      private final Map<KeYlessMethodCall, List<String>> methodReturnPathEntries = new LinkedHashMap<KeYlessMethodCall, List<String>>();
      
      /**
       * Maps an {@link KeYlessStart} to the path entries of its terminations.
       */
      private final Map<KeYlessStart, List<String>> terminationPathEntries = new LinkedHashMap<KeYlessStart, List<String>>();
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         AbstractKeYlessExecutionNode parent = parentNodeStack.peekFirst();
         if (isConstraint(uri, localName, qName)) {
            Object parentValue = parentVariableValueStack.peekFirst();
            if (parentValue != null) {
               if (!(parentValue instanceof KeYlessValue)) {
                  throw new SAXException("Can't add constraint to variable.");
               }
               KeYlessConstraint constraint = new KeYlessConstraint(getName(attributes));
               ((KeYlessValue) parentValue).addConstraint(constraint);
            }
            else {
               if (!(parent instanceof AbstractKeYlessExecutionNode)) {
                  throw new SAXException("Can't add constraint to non execution node.");
               }
               KeYlessConstraint constraint = new KeYlessConstraint(getName(attributes));
               ((AbstractKeYlessExecutionNode) parent).addConstraint(constraint);
            }
         }
         else if (isVariable(uri, localName, qName)) {
            Object parentValue = parentVariableValueStack.peekFirst();
            KeYlessVariable variable = createVariable(parentValue instanceof KeYlessValue ? (KeYlessValue)parentValue : null, uri, localName, qName, attributes);
            if (parentValue != null) {
               ((KeYlessValue)parentValue).addChildVariable(variable);
            }
            else {
               if (parent instanceof AbstractKeYlessStateNode<?>) {
                  ((AbstractKeYlessStateNode<?>)parent).addVariable(variable);
               }
               else {
                  throw new SAXException("Can't add variable to parent execution node.");
               }
            }
            parentVariableValueStack.addFirst(variable);
         }
         else if (isValue(uri, localName, qName)) {
            Object parentValue = parentVariableValueStack.peekFirst();
            if (!(parentValue instanceof KeYlessVariable)) {
               throw new SAXException("Can't add value to parent variable.");
            }
            KeYlessValue value = createValue((KeYlessVariable)parentValue, uri, localName, qName, attributes);
            ((KeYlessVariable)parentValue).addValue(value);
            parentVariableValueStack.addFirst(value);
         }
         else if (isCallStackEntry(uri, localName, qName)) {
            List<String> callStackEntries = callStackPathEntries.get(parent);
            if (callStackEntries == null) {
               callStackEntries = new LinkedList<String>();
               callStackPathEntries.put(parent, callStackEntries);
            }
            callStackEntries.add(getPathInTree(attributes));
         }
         else if (isMethodReturnEntry(uri, localName, qName)) {
            List<String> methodReturnEntries = methodReturnPathEntries.get(parent);
            if (methodReturnEntries == null) {
               methodReturnEntries = new LinkedList<String>();
               methodReturnPathEntries.put((KeYlessMethodCall)parent, methodReturnEntries);
            }
            methodReturnEntries.add(0, getPathInTree(attributes));
         }
         else if (isTerminationEntry(uri, localName, qName)) {
            List<String> terminationEntries = terminationPathEntries.get(parent);
            if (terminationEntries == null) {
               terminationEntries = new LinkedList<String>();
               terminationPathEntries.put((KeYlessStart)parent, terminationEntries);
            }
            terminationEntries.add(0, getPathInTree(attributes));
         }
         else if (isMethodReturnValue(uri, localName, qName)) {
            Object parentValue = parentNodeStack.peekFirst();
            if (!(parentValue instanceof KeYlessMethodReturn)) {
               throw new SAXException("Can't add method return value to parent.");
            }
            KeYlessMethodReturnValue returnValue = createMethodReturnValue(uri, localName, qName, attributes);
            ((KeYlessMethodReturn)parentValue).addReturnValue(returnValue);
         }
         else {
            AbstractKeYlessExecutionNode child = createExecutionNode(parent, uri, localName, qName, attributes);
            if (root == null) {
               root = child;
            }
            if (parent != null) {
               parent.addChild(child);
            }
            parentNodeStack.addFirst(child);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (isConstraint(uri, localName, qName)) {
            // Nothing to do.
         }
         else if (isVariable(uri, localName, qName)) {
            parentVariableValueStack.removeFirst();
         }
         else if (isValue(uri, localName, qName)) {
            parentVariableValueStack.removeFirst();
         }
         else if (isCallStackEntry(uri, localName, qName)) {
            // Nothing to do.
         }
         else if (isMethodReturnEntry(uri, localName, qName)) {
            // Nothing to do.
         }
         else if (isTerminationEntry(uri, localName, qName)) {
            // Nothing to do.
         }
         else if (isMethodReturnValue(uri, localName, qName)) {
            // Nothing to do.
         }
         else {
            parentNodeStack.removeFirst();
         }
      }
      
      /**
       * Returns the root of the read symbolic execution tree.
       * @return The root of the read symbolic execution tree.
       */
      public IExecutionNode getRoot() {
         return root;
      }

      /**
       * Returns the mapping of an {@link AbstractKeYlessExecutionNode} to its call stack entries.
       * @return The mapping of an {@link AbstractKeYlessExecutionNode} to its call stack entries.
       */
      public Map<AbstractKeYlessExecutionNode, List<String>> getCallStackPathEntries() {
         return callStackPathEntries;
      }

      /**
       * Returns the mapping of a {@link KeYlessMethodCall} to its method return entries.
       * @return The mapping of a {@link KeYlessMethodCall} to its method return entries.
       */
      public Map<KeYlessMethodCall, List<String>> getMethodReturnPathEntries() {
         return methodReturnPathEntries;
      }

      /**
       * Returns the mapping of a {@link KeYlessStart} to its termination entries.
       * @return The mapping of a {@link KeYlessStart} to its termination entries.
       */
      public Map<KeYlessStart, List<String>> getTerminationPathEntries() {
         return terminationPathEntries;
      }
   }
   
   /**
    * Checks if the currently parsed tag represents an {@link IExecutionConstraint}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link IExecutionConstraint}, {@code false} is something else.
    */
   protected boolean isConstraint(String uri, String localName, String qName) {
      return ExecutionNodeWriter.TAG_CONSTRAINT.equals(qName);
   }
   
   /**
    * Checks if the currently parsed tag represents an {@link IExecutionVariable}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link IExecutionVariable}, {@code false} is something else.
    */
   protected boolean isVariable(String uri, String localName, String qName) {
      return ExecutionNodeWriter.TAG_VARIABLE.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an {@link IExecutionMethodReturnValue}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link IExecutionMethodReturnValue}, {@code false} is something else.
    */
   protected boolean isMethodReturnValue(String uri, String localName, String qName) {
      return ExecutionNodeWriter.TAG_METHOD_RETURN_VALUE.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an {@link IExecutionValue}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link IExecutionValue}, {@code false} is something else.
    */
   protected boolean isValue(String uri, String localName, String qName) {
      return ExecutionNodeWriter.TAG_VALUE.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an entry of {@link IExecutionNode#getCallStack()}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents call stack entry, {@code false} is something else.
    */
   protected boolean isCallStackEntry(String uri, String localName, String qName) {
      return ExecutionNodeWriter.TAG_CALL_STACK_ENTRY.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an entry of {@link IExecutionMethodCall#getMethodReturns()}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents method return entry, {@code false} is something else.
    */
   protected boolean isMethodReturnEntry(String uri, String localName, String qName) {
      return ExecutionNodeWriter.TAG_METHOD_RETURN_ENTRY.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an entry of {@link IExecutionStart#getTerminations()}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents termination entry, {@code false} is something else.
    */
   protected boolean isTerminationEntry(String uri, String localName, String qName) {
      return ExecutionNodeWriter.TAG_TERMINATION_ENTRY.equals(qName);
   }

   /**
    * Creates a new {@link IExecutionVariable} with the given content.
    * @param parentValue The parent {@link IExecutionValue}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @param attributes The attributes.
    * @return The created {@link IExecutionVariable}.
    */
   protected KeYlessVariable createVariable(IExecutionValue parentValue,
                                            String uri, 
                                            String localName, 
                                            String qName, 
                                            Attributes attributes) {
      return new KeYlessVariable(parentValue, 
                                 isArrayIndex(attributes), 
                                 getArrayIndex(attributes), 
                                 getName(attributes));
   }
   
   /**
    * Creates a new {@link IExecutionMethodReturnValue} with the given content.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @param attributes The attributes.
    * @return The created {@link IExecutionMethodReturnValue}.
    */
   public KeYlessMethodReturnValue createMethodReturnValue(String uri, 
                                                           String localName,
                                                           String qName, 
                                                           Attributes attributes) {
      return new KeYlessMethodReturnValue(getName(attributes), 
                                          getReturnValueString(attributes), 
                                          getHasCondition(attributes), 
                                          getConditionString(attributes));
   }

   /**
    * Creates a new {@link IExecutionValue} with the given content.
    * @param parentVariable The parent {@link IExecutionVariable}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @param attributes The attributes.
    * @return The created {@link IExecutionValue}.
    */
   protected KeYlessValue createValue(IExecutionVariable parentVariable,
                                      String uri, 
                                      String localName, 
                                      String qName, 
                                      Attributes attributes) {
      return new KeYlessValue(parentVariable, 
                              getTypeString(attributes), 
                              getValueString(attributes), 
                              getName(attributes),
                              isValueUnknown(attributes),
                              isValueAnObject(attributes),
                              getConditionString(attributes));
   }

   /**
    * Creates a new {@link IExecutionNode} with the given content.
    * @param parent The parent {@link IExecutionNode}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @param attributes The attributes.
    * @return The created {@link IExecutionNode}.
    * @throws SAXException Occurred Exception.
    */
   protected AbstractKeYlessExecutionNode createExecutionNode(IExecutionNode parent, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      if (ExecutionNodeWriter.TAG_BRANCH_CONDITION.equals(qName)) {
         return new KeYlessBranchCondition(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes), getBranchCondition(attributes), isMergedBranchCondition(attributes), isBranchConditionComputed(attributes), getAdditionalBranchLabel(attributes));
      }
      else if (ExecutionNodeWriter.TAG_BRANCH_STATEMENT.equals(qName)) {
         return new KeYlessBranchStatement(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes));
      }
      else if (ExecutionNodeWriter.TAG_LOOP_CONDITION.equals(qName)) {
         return new KeYlessLoopCondition(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes));
      }
      else if (ExecutionNodeWriter.TAG_LOOP_STATEMENT.equals(qName)) {
         return new KeYlessLoopStatement(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes));
      }
      else if (ExecutionNodeWriter.TAG_METHOD_CALL.equals(qName)) {
         return new KeYlessMethodCall(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes));
      }
      else if (ExecutionNodeWriter.TAG_METHOD_RETURN.equals(qName)) {
         return new KeYlessMethodReturn(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes), getNameIncludingReturnValue(attributes), getSignature(attributes), getSignatureIncludingReturnValue(attributes), isReturnValueComputed(attributes), getMethodReturnCondition(attributes));
      }
      else if (ExecutionNodeWriter.TAG_EXCEPTIONAL_METHOD_RETURN.equals(qName)) {
         return new KeYlessExceptionalMethodReturn(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes), getSignature(attributes), getMethodReturnCondition(attributes));
      }
      else if (ExecutionNodeWriter.TAG_START.equals(qName)) {
         return new KeYlessStart(getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes));
      }
      else if (ExecutionNodeWriter.TAG_STATEMENT.equals(qName)) {
         return new KeYlessStatement(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes));
      }
      else if (ExecutionNodeWriter.TAG_TERMINATION.equals(qName)) {
         return new KeYlessTermination(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes), getTerminationKind(attributes), getBranchVerified(attributes));
      }
      else if (ExecutionNodeWriter.TAG_OPERATION_CONTRACT.equals(qName)) {
         return new KeYlessOperationContract(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes), isPreconditionComplied(attributes), isHasNotNullCheck(attributes), isNotNullCheckComplied(attributes), getResultTerm(attributes), getExceptionTerm(attributes), getSelfTerm(attributes), getContractParameters(attributes));
      }
      else if (ExecutionNodeWriter.TAG_LOOP_INVARIANT.equals(qName)) {
         return new KeYlessLoopInvariant(parent, getName(attributes), getPathCondition(attributes), isPathConditionChanged(attributes), isInitiallyValid(attributes));
      }
      else {
         throw new SAXException("Unknown tag \"" + qName + "\".");
      }
   }

   /**
    * Returns the additional branch label value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getAdditionalBranchLabel(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_ADDITIONAL_BRANCH_LABEL);
   }

   /**
    * Returns the path in tree value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getPathInTree(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_PATH_IN_TREE);
   }

   /**
    * Returns the name value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getName(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_NAME);
   }
   
   /**
    * Returns the name value including return value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getNameIncludingReturnValue(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_NAME_INCLUDING_RETURN_VALUE);
   }
   
   /**
    * Returns the signature value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getSignature(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_SIGNATURE);
   }
   
   /**
    * Returns the signature value including return value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getSignatureIncludingReturnValue(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_SIGNATURE_INCLUDING_RETURN_VALUE);
   }
   
   /**
    * Returns the termination kind value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected TerminationKind getTerminationKind(Attributes attributes) {
      return TerminationKind.valueOf(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_TERMINATION_KIND));
   }
   
   /**
    * Returns the precondition complied value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isPreconditionComplied(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_PRECONDITION_COMPLIED));
   }
   
   /**
    * Returns the has not null check value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isHasNotNullCheck(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_HAS_NOT_NULL_CHECK));
   }
   
   /**
    * Returns the is return value computed value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isReturnValueComputed(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_RETURN_VALUE_COMPUTED));
   }

   /**
    * Returns the is branch condition computed value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isBranchConditionComputed(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_BRANCH_CONDITION_COMPUTED));
   }
   
   /**
    * Returns the not null check complied value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isNotNullCheckComplied(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_NOT_NULL_CHECK_COMPLIED));
   }
   
   /**
    * Returns the initially valid value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isInitiallyValid(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_INITIALLY_VALID));
   }

   /**
    * Returns the is value an object value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isValueAnObject(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_IS_VALUE_AN_OBJECT));
   }

   /**
    * Returns the is value unknown value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isValueUnknown(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_IS_VALUE_UNKNOWN));
   }

   /**
    * Returns the value string value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getValueString(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_VALUE_STRING);
   }

   /**
    * Returns the value condition string value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getConditionString(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_CONDITION_STRING);
   }

   /**
    * Returns the is has condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean getHasCondition(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_HAS_CONDITION));
   }

   /**
    * Returns the is branch verified value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean getBranchVerified(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_BRANCH_VERIFIED));
   }

   /**
    * Returns the return value string value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getReturnValueString(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_RETURN_VALUE_STRING);
   }

   /**
    * Returns the type string value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getTypeString(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_TYPE_STRING);
   }

   /**
    * Returns the exception term value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getExceptionTerm(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_EXCEPTION_TERM);
   }

   /**
    * Returns the result term value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getResultTerm(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_RESULT_TERM);
   }

   /**
    * Returns the self term value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getSelfTerm(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_SELF_TERM);
   }

   /**
    * Returns the contract parameters value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getContractParameters(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_CONTRACT_PARAMETERS);
   }

   /**
    * Returns the array index value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected int getArrayIndex(Attributes attributes) {
      return Integer.parseInt(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_ARRAY_INDEX));
   }

   /**
    * Returns the is array index value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isArrayIndex(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_IS_ARRAY_INDEX));
   }
   
   /**
    * Returns the branch condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getBranchCondition(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_BRANCH_CONDITION);
   }

   /**
    * Returns the path condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getPathCondition(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_PATH_CONDITION);
   }

   /**
    * Returns the method return condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getMethodReturnCondition(Attributes attributes) {
      return attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_METHOD_RETURN_CONDITION);
   }

   /**
    * Returns the path condition changed value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isPathConditionChanged(Attributes attributes) {
      return Boolean.valueOf(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_PATH_CONDITION_CHANGED));
   }

   /**
    * Returns the merged branch condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isMergedBranchCondition(Attributes attributes) {
      return Boolean.valueOf(attributes.getValue(ExecutionNodeWriter.ATTRIBUTE_MERGED_BRANCH_CONDITION));
   }
   
   /**
    * An abstract implementation of {@link IExecutionElement} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static abstract class AbstractKeYlessExecutionElement implements IExecutionElement {
      /**
       * The name.
       */
      private final String name;
      
      /**
       * Constructor.
       * @param name The name of this node.
       */
      public AbstractKeYlessExecutionElement(String name) {
         this.name = name;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public KeYMediator getMediator() {
         return null;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public Services getServices() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Proof getProof() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Node getProofNode() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public NodeInfo getProofNodeInfo() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getName() {
         return name;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return getElementType() + " " + getName();
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isDisposed() {
         return false;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ITreeSettings getSettings() {
         return null;
      }
   }
   
   /**
    * An abstract implementation of {@link IExecutionNode} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static abstract class AbstractKeYlessExecutionNode extends AbstractKeYlessExecutionElement implements IExecutionNode {
      /**
       * The parent {@link IExecutionNode}.
       */
      private final IExecutionNode parent;
      
      /**
       * The children.
       */
      private final List<IExecutionNode> children = new LinkedList<IExecutionNode>();

      /**
       * The formated path condition.
       */
      private final String formatedPathCondition;
      
      /**
       * Is the path condition changed compared to parent?
       */
      private final boolean pathConditionChanged;
      
      /**
       * The call stack.
       */
      private final List<IExecutionNode> callStack = new LinkedList<IExecutionNode>();
      
      /**
       * The contained constraints.
       */
      private final List<IExecutionConstraint> constraints = new LinkedList<IExecutionConstraint>();
      
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       */
      public AbstractKeYlessExecutionNode(IExecutionNode parent, 
                                          String name, 
                                          String formatedPathCondition, 
                                          boolean pathConditionChanged) {
         super(name);
         this.parent = parent;
         this.formatedPathCondition = formatedPathCondition;
         this.pathConditionChanged = pathConditionChanged;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionNode getParent() {
         return parent;
      }
      
      /**
       * Adds the given child.
       * @param child The child to add.
       */
      public void addChild(IExecutionNode child) {
         children.add(child);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionNode[] getChildren() {
         return children.toArray(new IExecutionNode[children.size()]);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getPathCondition() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedPathCondition() throws ProofInputException {
         return formatedPathCondition;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isPathConditionChanged() {
         return pathConditionChanged;
      }
      
      /**
       * Adds the given entry to the call stack.
       * @param entry The entry to add to the call stack.
       */
      public void addCallStackEntry(IExecutionNode entry) {
         callStack.add(entry);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionNode[] getCallStack() {
         return callStack.isEmpty() ? null : callStack.toArray(new IExecutionNode[callStack.size()]);
      }

      /**
       * Adds the given {@link IExecutionConstraint}.
       * @param constraint The {@link IExecutionConstraint} to add.
       */
      public void addConstraint(IExecutionConstraint constraint) {
         constraints.add(constraint);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionConstraint[] getConstraints() {
         return constraints.toArray(new IExecutionConstraint[constraints.size()]);
      }
   }
   
   /**
    * An implementation of {@link IExecutionLoopCondition} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessBranchCondition extends AbstractKeYlessExecutionNode implements IExecutionBranchCondition {
      /**
       * The formated branch condition.
       */
      private final String formatedBranchCondition;
      
      /**
       * Merged branch condition?
       */
      private final boolean mergedBranchCondition;
      
      /**
       * Indicates if branch condition is computed or not.
       */
      private final boolean branchConditionComputed;

      /**
       * The optional additional branch label.
       */
      private final String additionalBranchLabel;
      
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       * @param formatedBranchCondition The formated branch condition.
       * @param mergedBranchCondition Merged branch condition?
       * @param branchConditionComputed Is branch condition computed?
       * @param additionalBranchLabel The optional additional branch label.
       */
      public KeYlessBranchCondition(IExecutionNode parent, 
                                    String name, 
                                    String formatedPathCondition, 
                                    boolean pathConditionChanged,
                                    String formatedBranchCondition,
                                    boolean mergedBranchCondition,
                                    boolean branchConditionComputed,
                                    String additionalBranchLabel) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
         this.formatedBranchCondition = formatedBranchCondition;
         this.mergedBranchCondition = mergedBranchCondition;
         this.branchConditionComputed = branchConditionComputed;
         this.additionalBranchLabel = additionalBranchLabel;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Branch Condition";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getBranchCondition() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedBranchCondition() {
         return formatedBranchCondition;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isMergedBranchCondition() {
         return mergedBranchCondition;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Node[] getMergedProofNodes() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term[] getMergedBranchCondtions() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isBranchConditionComputed() {
         return branchConditionComputed;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getAdditionalBranchLabel() {
         return additionalBranchLabel;
      }
   }

   /**
    * An implementation of {@link IExecutionStart} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessStart extends AbstractKeYlessExecutionNode implements IExecutionStart {
      /**
       * The up to now discovered {@link IExecutionTermination}s.
       */
      private ImmutableList<IExecutionTermination> terminations = ImmutableSLList.nil();
      
      /**
       * Constructor.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       */
      public KeYlessStart(String name, 
                          String formatedPathCondition, 
                          boolean pathConditionChanged) {
         super(null, name, formatedPathCondition, pathConditionChanged);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Start";
      }
      
      /**
       * Adds the given {@link IExecutionTermination}.
       * @param termination The {@link IExecutionTermination} to add.
       */
      public void addTermination(IExecutionTermination termination) {
         if (termination != null) {
            terminations = terminations.prepend(termination);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<IExecutionTermination> getTerminations() {
         return terminations;
      }
   }
   
   /**
    * An implementation of {@link IExecutionTermination} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessTermination extends AbstractKeYlessStateNode<SourceElement> implements IExecutionTermination {
      /**
       * The {@link TerminationKind}.
       */
      private final TerminationKind terminationKind;
      
      /**
       * The branch verified flag.
       */
      private final boolean branchVerified;
      
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       * @param exceptionalTermination Exceptional termination?
       * @param branchVerified The branch verified flag.
       */
      public KeYlessTermination(IExecutionNode parent, 
                                String name, 
                                String formatedPathCondition, 
                                boolean pathConditionChanged, 
                                TerminationKind terminationKind,
                                boolean branchVerified) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
         this.terminationKind = terminationKind;
         this.branchVerified = branchVerified;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IProgramVariable getExceptionVariable() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Sort getExceptionSort() {
         return null;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         switch (getTerminationKind()) {
            case EXCEPTIONAL : return "Exceptional Termination";
            case LOOP_BODY : return "Loop Body Termination";
            default : return "Termination";
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public TerminationKind getTerminationKind() {
         return terminationKind;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isBranchVerified() {
         return branchVerified;
      }
   }

   /**
    * An abstract implementation of {@link IExecutionStateNode} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static abstract class AbstractKeYlessStateNode<S extends SourceElement> extends AbstractKeYlessExecutionNode implements IExecutionStateNode<S> {
      /**
       * The contained variables.
       */
      private final List<IExecutionVariable> variables = new LinkedList<IExecutionVariable>();
      
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       */
      public AbstractKeYlessStateNode(IExecutionNode parent, 
                                      String name, 
                                      String formatedPathCondition,
                                      boolean pathConditionChanged) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
      }

      /**
       * Adds the given {@link IExecutionVariable}.
       * @param variable The {@link IExecutionVariable} to add.
       */
      public void addVariable(IExecutionVariable variable) {
         variables.add(variable);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public S getActiveStatement() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public PositionInfo getActivePositionInfo() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionVariable[] getVariables() {
         return variables.toArray(new IExecutionVariable[variables.size()]);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int getLayoutsCount() throws ProofInputException {
         return 0;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ISymbolicLayout getInitialLayout(int configurationIndex) throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ISymbolicLayout getCurrentLayout(int configurationIndex) throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<ISymbolicEquivalenceClass> getLayoutsEquivalenceClasses(int configurationIndex) throws ProofInputException {
         return null;
      }
   }
   
   /**
    * An implementation of {@link IExecutionBranchStatement} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessBranchStatement extends AbstractKeYlessStateNode<BranchStatement> implements IExecutionBranchStatement {
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       */
      public KeYlessBranchStatement(IExecutionNode parent, 
                                    String name, 
                                    String formatedPathCondition,
                                    boolean pathConditionChanged) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Branch Statement";
      }
   }
   
   /**
    * An implementation of {@link IExecutionLoopCondition} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessLoopCondition extends AbstractKeYlessStateNode<LoopStatement> implements IExecutionLoopCondition {
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       */
      public KeYlessLoopCondition(IExecutionNode parent, 
                                  String name, 
                                  String formatedPathCondition,
                                  boolean pathConditionChanged) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Expression getGuardExpression() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public PositionInfo getGuardExpressionPositionInfo() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Loop Condition";
      }
   }

   /**
    * An implementation of {@link IExecutionLoopStatement} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessLoopStatement extends AbstractKeYlessStateNode<LoopStatement> implements IExecutionLoopStatement {
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       */
      public KeYlessLoopStatement(IExecutionNode parent, 
                                  String name, 
                                  String formatedPathCondition, 
                                  boolean pathConditionChanged) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Loop Statement";
      }
   }

   /**
    * An implementation of {@link IExecutionMethodCall} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessMethodCall extends AbstractKeYlessStateNode<MethodBodyStatement> implements IExecutionMethodCall {
      /**
       * The up to now discovered {@link IExecutionBaseMethodReturn<?>}s.
       */
      private ImmutableList<IExecutionBaseMethodReturn<?>> methodReturns = ImmutableSLList.nil();
      
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       */
      public KeYlessMethodCall(IExecutionNode parent, 
                               String name, 
                               String formatedPathCondition,
                               boolean pathConditionChanged) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public MethodReference getMethodReference() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IProgramMethod getProgramMethod() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Method Call";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isImplicitConstructor() {
         return false;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public MethodReference getExplicitConstructorMethodReference() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IProgramMethod getExplicitConstructorProgramMethod() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<IExecutionBaseMethodReturn<?>> getMethodReturns() {
         return methodReturns;
      }
      
      /**
       * Adds the given {@link IExecutionBaseMethodReturn<?>}.
       * @param methodReturn The {@link IExecutionBaseMethodReturn<?>} to add.
       */
      public void addMethodReturn(IExecutionBaseMethodReturn<?> methodReturn) {
         if (methodReturn != null) {
            methodReturns = methodReturns.prepend(methodReturn);
         }
      }
   }

   /**
    * An implementation of {@link IExecutionExceptionalMethodReturn} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessExceptionalMethodReturn extends AbstractKeYlessStateNode<Throw> implements IExecutionExceptionalMethodReturn {
      /**
       * The signature.
       */
      private final String signature;

      /**
       * The formated method return condition.
       */
      private final String formatedMethodReturn;

      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       * @param signature The signature.
       * @param formatedMethodReturn The formated method return condition.
       */
      public KeYlessExceptionalMethodReturn(IExecutionNode parent, 
                                            String name, 
                                            String formatedPathCondition, 
                                            boolean pathConditionChanged,
                                            String signature,
                                            String formatedMethodReturn) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
         this.signature = signature;
         this.formatedMethodReturn = formatedMethodReturn;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionMethodCall getMethodCall() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getSignature() throws ProofInputException {
         return signature;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Exceptional Method Return";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getMethodReturnCondition() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedMethodReturnCondition() throws ProofInputException {
         return formatedMethodReturn;
      }
   }

   /**
    * An implementation of {@link IExecutionMethodReturn} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessMethodReturn extends AbstractKeYlessStateNode<SourceElement> implements IExecutionMethodReturn {
      /**
       * The name including the return value.
       */
      private final String nameIncludingReturnValue;
      
      /**
       * The signature including the return value.
       */
      private final String signatureIncludingReturnValue;
      
      /**
       * Defines if the return value is computed or not.
       */
      private final boolean returnValueComputed;
      
      /**
       * The signature.
       */
      private final String signature;

      /**
       * The possible return values.
       */
      private final List<IExecutionMethodReturnValue> returnValues = new LinkedList<IExecutionMethodReturnValue>();

      /**
       * The formated method return condition.
       */
      private final String formatedMethodReturn;

      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param formatedPathCondition The formated path condition.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       * @param nameIncludingReturnValue The name including the return value.
       * @param signature The signature.
       * @param signatureIncludingReturnValue The signature including return value.
       * @param returnValueComputed Is the return value computed?
       * @param formatedMethodReturn The formated method return condition.
       */
      public KeYlessMethodReturn(IExecutionNode parent, 
                                 String name, 
                                 String formatedPathCondition, 
                                 boolean pathConditionChanged,
                                 String nameIncludingReturnValue,
                                 String signature,
                                 String signatureIncludingReturnValue,
                                 boolean returnValueComputed,
                                 String formatedMethodReturn) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
         this.nameIncludingReturnValue = nameIncludingReturnValue;
         this.signatureIncludingReturnValue = signatureIncludingReturnValue;
         this.returnValueComputed = returnValueComputed;
         this.signature = signature;
         this.formatedMethodReturn = formatedMethodReturn;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionMethodCall getMethodCall() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getNameIncludingReturnValue() throws ProofInputException {
         return nameIncludingReturnValue;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getSignature() throws ProofInputException {
         return signature;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getSignatureIncludingReturnValue() throws ProofInputException {
         return signatureIncludingReturnValue;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Method Return";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isReturnValuesComputed() {
         return returnValueComputed;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionMethodReturnValue[] getReturnValues() throws ProofInputException {
         return returnValues.toArray(new IExecutionMethodReturnValue[returnValues.size()]);
      }
      
      /**
       * Adds the given {@link IExecutionMethodReturnValue}.
       * @param returnValue The {@link IExecutionMethodReturnValue} to add.
       */
      public void addReturnValue(IExecutionMethodReturnValue returnValue) {
         returnValues.add(returnValue);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getMethodReturnCondition() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedMethodReturnCondition() throws ProofInputException {
         return formatedMethodReturn;
      }
   }
   
   /**
    * An implementation of {@link IExecutionMethodReturn} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessMethodReturnValue extends AbstractKeYlessExecutionElement implements IExecutionMethodReturnValue {
      /**
       * The human readable return value.
       */
      private final String returnValueString;
      
      /**
       * Is a condition available?
       */
      private final boolean hasCondition;
      
      /**
       * The optional human readable condition.
       */
      private final String conditionString;

      /**
       * Constructor.
       * @param name The name of this node.
       * @param returnValueString The human readable return value.
       * @param hasCondition Is a condition available?
       * @param conditionString The optional human readable condition.
       */
      public KeYlessMethodReturnValue(String name,
                                      String returnValueString,
                                      boolean hasCondition,
                                      String conditionString) {
         super(name);
         this.returnValueString = returnValueString;
         this.hasCondition = hasCondition;
         this.conditionString = conditionString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Return Value";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getReturnValue() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getReturnValueString() throws ProofInputException {
         return returnValueString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean hasCondition() throws ProofInputException {
         return hasCondition;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getCondition() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getConditionString() throws ProofInputException {
         return conditionString;
      }
   }

   /**
    * An implementation of {@link IExecutionStatement} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessStatement extends AbstractKeYlessStateNode<SourceElement> implements IExecutionStatement {
      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       * @param formatedPathCondition The formated path condition.
       */
      public KeYlessStatement(IExecutionNode parent, 
                              String name, 
                              String formatedPathCondition,
                              boolean pathConditionChanged) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Statement";
      }
   }

   /**
    * An implementation of {@link IExecutionOperationContract} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessOperationContract extends AbstractKeYlessStateNode<SourceElement> implements IExecutionOperationContract {
      /**
       * Is precondition complied?
       */
      private final boolean preconditionComplied;
      
      /**
       * Has not null check?
       */
      private final boolean hasNotNullCheck;
      
      /**
       * Is not null check complied?
       */
      private final boolean notNullCheckComplied;

      /**
       * The formated result term.
       */
      private final String formatedResultTerm;

      /**
       * The formated exception term.
       */
      private final String formatedExceptionTerm;

      /**
       * The formated self term.
       */
      private final String formatedSelfTerm;

      /**
       * The formated contract parameters.
       */
      private final String formatedContractParams;

      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       * @param formatedPathCondition The formated path condition.
       * @param preconditionComplied Is precondition complied?
       * @param hasNotNullCheck Has not null check?
       * @param notNullCheckComplied Is not null check complied?
       * @param formatedResultTerm The formated result term.
       * @param formatedExceptionTerm The formated exception term.
       * @param formatedSelfTerm The formated self term.
       * @param formatedContractParams The formated contract parameters.
       */
      public KeYlessOperationContract(IExecutionNode parent, 
                                      String name, 
                                      String formatedPathCondition,
                                      boolean pathConditionChanged,
                                      boolean preconditionComplied,
                                      boolean hasNotNullCheck,
                                      boolean notNullCheckComplied,
                                      String formatedResultTerm,
                                      String formatedExceptionTerm,
                                      String formatedSelfTerm,
                                      String formatedContractParams) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
         this.preconditionComplied = preconditionComplied;
         this.hasNotNullCheck = hasNotNullCheck;
         this.notNullCheckComplied = notNullCheckComplied;
         this.formatedResultTerm = formatedResultTerm;
         this.formatedExceptionTerm = formatedExceptionTerm;
         this.formatedSelfTerm = formatedSelfTerm;
         this.formatedContractParams = formatedContractParams;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Operation Contract";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Contract getContract() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IProgramMethod getContractProgramMethod() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isPreconditionComplied() {
         return preconditionComplied;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean hasNotNullCheck() {
         return hasNotNullCheck;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isNotNullCheckComplied() {
         return notNullCheckComplied;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getResultTerm() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getExceptionTerm() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedResultTerm() throws ProofInputException {
         return formatedResultTerm;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedExceptionTerm() throws ProofInputException {
         return formatedExceptionTerm;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getSelfTerm() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<Term> getContractParams() throws ProofInputException {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedSelfTerm() throws ProofInputException {
         return formatedSelfTerm;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getFormatedContractParams() throws ProofInputException {
         return formatedContractParams;
      }
   }

   /**
    * An implementation of {@link IExecutionLoopInvariant} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessLoopInvariant extends AbstractKeYlessStateNode<SourceElement> implements IExecutionLoopInvariant {
      /**
       * Initially valid?
       */
      private final boolean initiallyValid;

      /**
       * Constructor.
       * @param parent The parent {@link IExecutionNode}.
       * @param name The name of this node.
       * @param pathConditionChanged Is the path condition changed compared to parent?
       * @param formatedPathCondition The formated path condition.
       * @param initiallyValid Initially valid?
       */
      public KeYlessLoopInvariant(IExecutionNode parent, 
                                  String name, 
                                  String formatedPathCondition,
                                  boolean pathConditionChanged,
                                  boolean initiallyValid) {
         super(parent, name, formatedPathCondition, pathConditionChanged);
         this.initiallyValid = initiallyValid;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Loop Invariant";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public LoopInvariant getLoopInvariant() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public While getLoopStatement() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isInitiallyValid() {
         return initiallyValid;
      }
   }
   
   /**
    * An implementation of {@link IExecutionConstraint} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessConstraint extends AbstractKeYlessExecutionElement implements IExecutionConstraint {
      /**
       * Constructor.
       * @param name The name.
       */
      public KeYlessConstraint(String name) {
         super(name);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Constraint";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getTerm() {
         return null;
      }
   }
   
   /**
    * An implementation of {@link IExecutionVariable} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessVariable extends AbstractKeYlessExecutionElement implements IExecutionVariable {
      /**
       * The parent {@link IExecutionValue} if available.
       */
      private final IExecutionValue parentValue;
      
      /**
       * The is array flag.
       */
      private final boolean isArrayIndex;

      /**
       * The array index.
       */
      private final int arrayIndex;
      
      /**
       * The contained values.
       */
      private final List<IExecutionValue> values = new LinkedList<IExecutionValue>();
      
      /**
       * Constructor.
       * @param parentVariable The parent {@link IExecutionValue} if available.
       * @param isArrayIndex The is array flag.
       * @param arrayIndex The array index.
       * @param name The name.
       */
      public KeYlessVariable(IExecutionValue parentValue, 
                             boolean isArrayIndex, 
                             int arrayIndex, 
                             String name) {
         super(name);
         this.parentValue = parentValue;
         this.isArrayIndex = isArrayIndex;
         this.arrayIndex = arrayIndex;
      }
      
      /**
       * Adds the given child {@link IExecutionValue}.
       * @param variable The child {@link IExecutionValue} to add.
       */
      public void addValue(IExecutionValue variable) {
         values.add(variable);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionValue getParentValue() {
         return parentValue;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionValue[] getValues() {
         return values.toArray(new IExecutionValue[values.size()]);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int getArrayIndex() {
         return arrayIndex;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isArrayIndex() {
         return isArrayIndex;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IProgramVariable getProgramVariable() {
         return null;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Variable";
      }
   }
   
   /**
    * An implementation of {@link IExecutionValue} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessValue extends AbstractKeYlessExecutionElement implements IExecutionValue {
      /**
       * The parent {@link IExecutionVariable} if available.
       */
      private final IExecutionVariable variable;
      
      /**
       * The type string.
       */
      private final String typeString;
      
      /**
       * The value string.
       */
      private final String valueString;
      
      /**
       * Is the value unknown?
       */
      private final boolean valueUnknown;

      /**
       * Is the value an object?
       */
      private final boolean valueAnObject;
      
      /**
       * The child variables.
       */
      private final List<IExecutionVariable> childVariables = new LinkedList<IExecutionVariable>();

      /**
       * The condition as {@link String}.
       */
      private final String conditionString;
      
      /**
       * The related {@link IExecutionConstraint}s.
       */
      private final List<IExecutionConstraint> constraints = new LinkedList<IExecutionConstraint>();
      
      /**
       * Constructor.
       * @param variable The parent {@link IExecutionVariable}.
       * @param typeString The type string.
       * @param valueString The value string.
       * @param name The name.
       * @param valueUnknown Is the value unknown?
       * @param valueAnObject Is the value an object?
       * @param conditionString The condition as human readable {@link String}.
       */
      public KeYlessValue(IExecutionVariable variable, 
                          String typeString, 
                          String valueString, 
                          String name,
                          boolean valueUnknown,
                          boolean valueAnObject,
                          String conditionString) {
         super(name);
         this.variable = variable;
         this.typeString = typeString;
         this.valueString = valueString;
         this.valueUnknown = valueUnknown;
         this.valueAnObject = valueAnObject;
         this.conditionString = conditionString;
      }
      
      /**
       * Adds the given child {@link IExecutionVariable}.
       * @param variable The child {@link IExecutionVariable} to add.
       */
      public void addChildVariable(IExecutionVariable variable) {
         childVariables.add(variable);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getValueString() throws ProofInputException {
         return valueString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getTypeString() {
         return typeString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getConditionString() throws ProofInputException {
         return conditionString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionVariable getVariable() {
         return variable;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionVariable[] getChildVariables() throws ProofInputException {
         return childVariables.toArray(new IExecutionVariable[childVariables.size()]);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isValueUnknown() throws ProofInputException {
         return valueUnknown;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isValueAnObject() throws ProofInputException {
         return valueAnObject;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getValue() throws ProofInputException {
         return null;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getElementType() {
         return "Value";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getCondition() throws ProofInputException {
         return null;
      }
      
      /**
       * Adds the given {@link IExecutionConstraint}.
       * @param constraint The {@link IExecutionConstraint} to add.
       */
      public void addConstraint(IExecutionConstraint constraint) {
         constraints.add(constraint);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IExecutionConstraint[] getConstraints() throws ProofInputException {
         return constraints.toArray(new IExecutionConstraint[constraints.size()]);
      }
   }
}