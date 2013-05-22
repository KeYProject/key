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
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.ISEDMemoryStackFrameCompatibleDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchNode;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;
import org.key_project.sed.core.model.memory.SEDMemoryLoopBodyTermination;
import org.key_project.sed.core.model.memory.SEDMemoryLoopCondition;
import org.key_project.sed.core.model.memory.SEDMemoryLoopNode;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.core.model.memory.SEDMemoryUseLoopInvariant;
import org.key_project.sed.core.model.memory.SEDMemoryUseOperationContract;
import org.key_project.sed.core.model.memory.SEDMemoryValue;
import org.key_project.sed.core.model.memory.SEDMemoryVariable;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * <p>
 * Instances of this class are used to read proprietary XML file
 * created via {@link SEDXMLWriter}. The result is a {@link List} of
 * contained {@link ISEDDebugTarget}s. The created instances are memory
 * instances and contains only the saved values. An execution at runtime, like
 * termination, step over, etc. is not possible.
 * </p>
 * <p>
 * The main use case of the serialization is to persistent an actual
 * {@link ISEDDebugTarget} as oracle file which is later used in test cases
 * to compare a given {@link ISEDDebugTarget} with the loaded instance
 * of the oracle file.
 * </p>
 * @author Martin Hentschel
 * @see SEDXMLWriter
 */
public class SEDXMLReader {
   /**
    * Parses the given XML content.
    * @param xml The XML content to parse.
    * @return The contained {@link ISEDDebugTarget}s in the given XML content.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public List<ISEDDebugTarget> read(String xml) throws ParserConfigurationException, SAXException, IOException {
      return xml != null ? read(new ByteArrayInputStream(xml.getBytes())) : null;
   }
   
   /**
    * Parses the given XML content.
    * @param xml The XML content to parse.
    * @return The contained {@link ISEDDebugTarget}s in the given XML content.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public List<ISEDDebugTarget> read(IFile file) throws ParserConfigurationException, SAXException, IOException, CoreException {
      return file != null ? read(file.getContents()) : null;
   }
   
   /**
    * Parses the given XML content defined by the {@link InputStream}.
    * @param in The {@link InputStream} with the XML content to parse.
    * @return The contained {@link ISEDDebugTarget}s in the given XML content.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public List<ISEDDebugTarget> read(InputStream in) throws ParserConfigurationException, SAXException, IOException {
      if (in != null) {
         try {
            // Parse XML document
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setNamespaceAware(true);
            SAXParser saxParser = factory.newSAXParser();
            SEDSAXHandler handler = new SEDSAXHandler();
            saxParser.parse(in, handler);
            // Create call stacks
            Set<Entry<ISEDMemoryDebugNode, List<String>>> entries = handler.getCallStackEntriesMap().entrySet();
            for (Entry<ISEDMemoryDebugNode, List<String>> entry : entries) {
               List<ISEDDebugNode> callStack = new LinkedList<ISEDDebugNode>();
               for (String nodeRefId : entry.getValue()) {
                  ISEDDebugElement element = handler.getElementById(nodeRefId);
                  if (element == null) {
                     throw new SAXException("Referenced node with ID \"" + nodeRefId + "\" is not available in model.");
                  }
                  if (!(element instanceof ISEDDebugNode)) {
                     throw new SAXException("Referenced node with ID \"" + nodeRefId + "\" refers to wrong model object \"" + element + "\".");
                  }
                  callStack.add((ISEDDebugNode)element);
               }
               entry.getKey().setCallStack(callStack.toArray(new ISEDDebugNode[callStack.size()]));
            }
            // Return result
            return handler.getResult();
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
    * SAX implementation of {@link DefaultHandler} used to parse XML content
    * created via {@link SEDXMLWriter}.
    * @author Martin Hentschel
    */
   private class SEDSAXHandler extends DefaultHandler {
      /**
       * The found {@link ISEDDebugTarget}s.
       */
      private List<ISEDDebugTarget> result = new LinkedList<ISEDDebugTarget>();
      
      /**
       * The current {@link SEDMemoryDebugTarget}.
       */
      private SEDMemoryDebugTarget target;
      
      /**
       * The current {@link SEDMemoryThread}.
       */
      private SEDMemoryThread thread;
      
      /**
       * The parent hierarchy filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private Deque<ISEDMemoryDebugNode> parentStack = new LinkedList<ISEDMemoryDebugNode>();
      
      /**
       * The parent hierarchy of variables and values filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private Deque<IDebugElement> variablesValueStack = new LinkedList<IDebugElement>();
      
      /**
       * Maps {@link ISEDMemoryDebugNode} to the IDs of their calls tacks.
       */
      private Map<ISEDMemoryDebugNode, List<String>> callStackEntriesMap = new HashMap<ISEDMemoryDebugNode, List<String>>();

      /**
       * Maps the element ID ({@link ISEDDebugElement#getId()}) to the its {@link ISEDDebugElement} instance.
       */
      private Map<String, ISEDDebugElement> elementIdMapping = new HashMap<String, ISEDDebugElement>();
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         ISEDMemoryDebugNode parent = parentStack.peekFirst();
         if (isCallStackEntry(uri, localName, qName)) {
            List<String> callStack = callStackEntriesMap.get(parent);
            if (callStack == null) {
               callStack = new LinkedList<String>();
               callStackEntriesMap.put(parent, callStack);
            }
            callStack.add(getNodeIdRef(attributes));
         }
         else {
            Object obj = createElement(target, parent != null ? parent : thread, thread, uri, localName, qName, attributes);
            if (obj instanceof ISEDDebugElement) {
               ISEDDebugElement element = (ISEDDebugElement)obj;
               elementIdMapping.put(element.getId(), element);
            }
            if (obj instanceof SEDMemoryDebugTarget) {
               target = (SEDMemoryDebugTarget)obj;
               result.add(target);
            }
            else if (obj instanceof IVariable) {
               IVariable variable = (IVariable)obj;
               if (variablesValueStack.isEmpty()) {
                  if (parent instanceof ISEDMemoryStackFrameCompatibleDebugNode) {
                     ((ISEDMemoryStackFrameCompatibleDebugNode)parent).addVariable(variable);
                  }
                  else {
                     throw new SAXException("Can't add variable to parent.");
                  }
               }
               else {
                  IDebugElement parentVariableOrValue = variablesValueStack.peekFirst();
                  if (parentVariableOrValue instanceof SEDMemoryValue) {
                     ((SEDMemoryValue)parentVariableOrValue).addVariable(variable);
                  }
                  else {
                     throw new SAXException("Can't add variable to parent.");
                  }
               }
               variablesValueStack.addFirst(variable);
            }
            else if (obj instanceof IValue) {
               IValue value = (IValue)obj;
               IDebugElement parentVariableOrValue = variablesValueStack.peekFirst();
               if (parentVariableOrValue instanceof SEDMemoryVariable) {
                  ((SEDMemoryVariable)parentVariableOrValue).setValue(value);
               }
               else {
                  throw new SAXException("Can't add value to parent.");
               }
               variablesValueStack.addFirst(value);
            }
            else if (obj instanceof SEDMemoryThread) {
               thread = (SEDMemoryThread)obj;
               if (target != null) {
                  target.addSymbolicThread(thread);
               }
               else {
                  throw new SAXException("Model is in inconsistent state.");
               }
            }
            else if (obj instanceof ISEDMemoryDebugNode) {
               ISEDMemoryDebugNode child = (ISEDMemoryDebugNode)obj; 
               parentStack.addFirst(child);
               if (parent != null) {
                  parent.addChild(child);
               }
               else if (thread != null) {
                  thread.addChild(child);
               }
               else {
                  throw new SAXException("Model is in inconsistent state.");
               }
            }
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (isVariable(uri, localName, qName) || isValue(uri, localName, qName)) {
            variablesValueStack.removeFirst();
         }
         else if (isCallStackEntry(uri, localName, qName)) {
            // Nothing to do
         }
         else {
            if (!parentStack.isEmpty()) {
               parentStack.removeFirst();
            }
            else if (thread != null) {
               thread = null;
            }
            else if (target != null) {
               target = null;
            }
            else if (SEDXMLWriter.TAG_LAUNCH.equals(qName)) {
               // Nothing to do, but still valid.
            }
            else {
               throw new SAXException("Model is in inconsistent state.");
            }
         }
      }

      /**
       * Returns the found {@link ISEDDebugTarget}s.
       * @return The found {@link ISEDDebugTarget}s.
       */
      public List<ISEDDebugTarget> getResult() {
         return result;
      }

      /**
       * Returns the mapping of {@link ISEDDebugNode}s to their call stacks.
       * @return The mapping of {@link ISEDDebugNode}s to their call stacks.
       */
      public Map<ISEDMemoryDebugNode, List<String>> getCallStackEntriesMap() {
         return callStackEntriesMap;
      }

      /**
       * Returns the instantiated {@link ISEDDebugElement} with the give ID.
       * @param id The ID.
       * @return The instantiated {@link ISEDDebugElement} or {@code null} if not available.
       */
      public ISEDDebugElement getElementById(String id) {
         return elementIdMapping.get(id);
      }
   }
   
   /**
    * Checks if the given tag name represents a call stack entry.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents a call stack entry, {@code false} represents something else.
    */
   protected boolean isCallStackEntry(String uri, String localName, String qName) {
      return SEDXMLWriter.TAG_CALL_STACK_ENTRY.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link IVariable}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link IVariable}, {@code false} represents something else.
    */
   protected boolean isVariable(String uri, String localName, String qName) {
      return SEDXMLWriter.TAG_VARIABLE.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link IValue}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link IValue}, {@code false} represents something else.
    */
   protected boolean isValue(String uri, String localName, String qName) {
      return SEDXMLWriter.TAG_VALUE.equals(qName);
   }
   
   /**
    * Creates an {@link Object} for the element defined by the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link Object}.
    * @throws SAXException Occurred Exception.
    */
   protected Object createElement(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      if (SEDXMLWriter.TAG_LAUNCH.equals(qName)) {
         return null; // Nothing to do
      }
      else if (SEDXMLWriter.TAG_DEBUG_TARGET.equals(qName)) {
         return createDebugTarget(uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_BRANCH_CONDITION.equals(qName)) {
         return createBranchCondition(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_BRANCH_NODE.equals(qName)) {
         return createBranchNode(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_EXCEPTIONAL_TERMINATION.equals(qName)) {
         return createExceptionalTermination(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_LOOP_BODY_TERMINATION.equals(qName)) {
         return createLoopBodyTermination(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_LOOP_CONDITION.equals(qName)) {
         return createLoopCondition(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_LOOP_NODE.equals(qName)) {
         return createLoopNode(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_METHOD_CALL.equals(qName)) {
         return createMethodCall(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_METHOD_RETURN.equals(qName)) {
         return createMethodReturn(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_STATEMENT.equals(qName)) {
         return createStatement(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_TERMINATION.equals(qName)) {
         return createTermination(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_THREAD.equals(qName)) {
         return createThread(target, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_VARIABLE.equals(qName)) {
         return createVariable(target, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_VALUE.equals(qName)) {
         return createValue(target, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_USE_OPERATION_CONTRACT.equals(qName)) {
         return createUseOperationContract(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_USE_LOOP_INVARIANT.equals(qName)) {
         return createUseLoopInvariant(target, parent, thread, uri, localName, qName, attributes);
      }
      else {
         throw new SAXException("Unknown tag \"" + qName + "\".");
      }
   }
   
   protected SEDMemoryValue createValue(ISEDDebugTarget target, String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryValue value = new SEDMemoryValue(target);
      value.setAllocated(isAllocated(attributes));
      value.setReferenceTypeName(getReferenceTypeName(attributes));
      value.setValueString(getValueString(attributes));
      value.setMultiValued(isMultiValued(attributes));
      return value;
   }
   
   protected SEDMemoryVariable createVariable(ISEDDebugTarget target, String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryVariable variable = new SEDMemoryVariable(target);
      variable.setName(getName(attributes));
      variable.setReferenceTypeName(getReferenceTypeName(attributes));
      return variable;
   }
   
   /**
    * Creates a {@link SEDMemoryBranchCondition} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryBranchCondition}.
    */
   protected SEDMemoryBranchCondition createBranchCondition(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryBranchCondition termination = new SEDMemoryBranchCondition(target, parent, thread);
      fillDebugNode(termination, attributes);
      return termination;
   }
   
   /**
    * Creates a {@link SEDMemoryDebugTarget} instance for the content in the given tag.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryDebugTarget}.
    */
   protected SEDMemoryDebugTarget createDebugTarget(String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
      target.setId(getId(attributes));
      target.setName(getName(attributes));
      target.setModelIdentifier(getModelIdentifier(attributes));
      return target;
   }

   /**
    * Creates a {@link SEDMemoryBranchNode} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryBranchNode}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryBranchNode createBranchNode(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryBranchNode methodReturn = new SEDMemoryBranchNode(target, parent, thread);
      fillDebugNode(methodReturn, attributes);
      fillStackFrame(methodReturn, attributes);
      return methodReturn;
   }
   
   /**
    * Creates a {@link SEDMemoryExceptionalTermination} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryExceptionalTermination}.
    */   
   protected SEDMemoryExceptionalTermination createExceptionalTermination(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryExceptionalTermination termination = new SEDMemoryExceptionalTermination(target, parent, thread);
      fillDebugNode(termination, attributes);
      return termination;
   }
   
   /**
    * Creates a {@link SEDMemoryLoopBodyTermination} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryLoopBodyTermination}.
    */   
   protected SEDMemoryLoopBodyTermination createLoopBodyTermination(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryLoopBodyTermination termination = new SEDMemoryLoopBodyTermination(target, parent, thread);
      fillDebugNode(termination, attributes);
      return termination;
   }
   
   /**
    * Creates a {@link SEDMemoryLoopCondition} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryLoopCondition}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryLoopCondition createLoopCondition(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryLoopCondition methodReturn = new SEDMemoryLoopCondition(target, parent, thread);
      fillDebugNode(methodReturn, attributes);
      fillStackFrame(methodReturn, attributes);
      return methodReturn;
   }
   
   /**
    * Creates a {@link SEDMemoryLoopNode} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryLoopNode}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryLoopNode createLoopNode(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryLoopNode methodReturn = new SEDMemoryLoopNode(target, parent, thread);
      fillDebugNode(methodReturn, attributes);
      fillStackFrame(methodReturn, attributes);
      return methodReturn;
   }
   
   /**
    * Creates a {@link SEDMemoryMethodCall} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryMethodCall}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryMethodCall createMethodCall(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryMethodCall methodReturn = new SEDMemoryMethodCall(target, parent, thread);
      fillDebugNode(methodReturn, attributes);
      fillStackFrame(methodReturn, attributes);
      return methodReturn;
   }
   
   /**
    * Creates a {@link SEDMemoryMethodReturn} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryMethodReturn}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryMethodReturn createMethodReturn(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryMethodReturn methodReturn = new SEDMemoryMethodReturn(target, parent, thread);
      fillDebugNode(methodReturn, attributes);
      fillStackFrame(methodReturn, attributes);
      return methodReturn;
   }
   
   /**
    * Creates a {@link SEDMemoryStatement} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryStatement createStatement(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryStatement statement = new SEDMemoryStatement(target, parent, thread);
      fillDebugNode(statement, attributes);
      fillStackFrame(statement, attributes);
      return statement;
   }
   
   /**
    * Creates a {@link SEDMemoryUseOperationContract} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryUseOperationContract createUseOperationContract(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryUseOperationContract useOperationContract = new SEDMemoryUseOperationContract(target, parent, thread);
      fillDebugNode(useOperationContract, attributes);
      fillStackFrame(useOperationContract, attributes);
      useOperationContract.setPreconditionComplied(isPreconditionComplied(attributes));
      useOperationContract.setHasNotNullCheck(hasNotNullCheck(attributes));
      useOperationContract.setNotNullCheckComplied(isNotNullCheckComplied(attributes));
      return useOperationContract;
   }
   
   /**
    * Creates a {@link SEDMemoryUseLoopInvariant} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryUseLoopInvariant createUseLoopInvariant(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryUseLoopInvariant useLoopInvariant = new SEDMemoryUseLoopInvariant(target, parent, thread);
      fillDebugNode(useLoopInvariant, attributes);
      fillStackFrame(useLoopInvariant, attributes);
      useLoopInvariant.setInitiallyValid(isInitiallyValid(attributes));
      return useLoopInvariant;
   }
   
   /**
    * Creates a {@link SEDMemoryTermination} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryTermination}.
    */   
   protected SEDMemoryTermination createTermination(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryTermination termination = new SEDMemoryTermination(target, parent, thread);
      fillDebugNode(termination, attributes);
      return termination;
   }
   
   /**
    * Creates a {@link SEDMemoryThread} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryThread}.
    */   
   protected SEDMemoryThread createThread(ISEDDebugTarget target, String uri, String localName, String qName, Attributes attributes) {
      SEDMemoryThread thread = new SEDMemoryThread(target);
      fillDebugNode(thread, attributes);
      return thread;
   }
   
   /**
    * Fills the attributes of the given {@link ISEDMemoryDebugNode}.
    * @param node The {@link ISEDMemoryDebugNode} to fill.
    * @param attributes The {@link Attributes} which provides the content.
    */
   protected void fillDebugNode(ISEDMemoryDebugNode node, Attributes attributes) {
      node.setId(getId(attributes));
      node.setName(getName(attributes));
      node.setPathCondition(getPathCondition(attributes));
   }
   
   /**
    * Fills the attributes of the given {@link ISEDMemoryStackFrameCompatibleDebugNode}.
    * @param node The {@link ISEDMemoryStackFrameCompatibleDebugNode} to fill.
    * @param attributes The {@link Attributes} which provides the content.
    * @throws SAXException Occurred Exception.
    */
   protected void fillStackFrame(ISEDMemoryStackFrameCompatibleDebugNode node, Attributes attributes) throws SAXException {
      node.setLineNumber(getLineNumber(attributes));
      node.setCharStart(getCharStart(attributes));
      node.setCharEnd(getCharEnd(attributes));
   }

   /**
    * Returns the ID value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */   
   protected String getId(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_ID);
   }
   
   /**
    * Returns the node id reference value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getNodeIdRef(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_NODE_ID_REF);
   }
   
   /**
    * Returns the name value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getName(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_NAME);
   }

   /**
    * Returns the path condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getPathCondition(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_PATH_CONDITION);
   }
   
   /**
    * Returns the model identifier value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getModelIdentifier(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_MODEL_IDENTIFIER);
   }
   
   /**
    * Returns the line number value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    * @throws SAXException Occurred Exception.
    */
   protected int getLineNumber(Attributes attributes) throws SAXException {
      try {
         return Integer.parseInt(attributes.getValue(SEDXMLWriter.ATTRIBUTE_LINE_NUMBER));
      }
      catch (NumberFormatException e) {
         throw new SAXException(e);
      }
   }
   
   /**
    * Returns the char start value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    * @throws SAXException Occurred Exception.
    */
   protected int getCharStart(Attributes attributes) throws SAXException {
      try {
         return Integer.parseInt(attributes.getValue(SEDXMLWriter.ATTRIBUTE_CHAR_START));
      }
      catch (NumberFormatException e) {
         throw new SAXException(e);
      }
   }
   
   /**
    * Returns the char end value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    * @throws SAXException Occurred Exception.
    */
   protected int getCharEnd(Attributes attributes) throws SAXException {
      try {
         return Integer.parseInt(attributes.getValue(SEDXMLWriter.ATTRIBUTE_CHAR_END));
      }
      catch (NumberFormatException e) {
         throw new SAXException(e);
      }
   }
   
   /**
    * Returns the multi valued value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isMultiValued(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_MULTI_VALUED));
   }
   
   /**
    * Returns the allocated value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isAllocated(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_ALLOCATED));
   }
   
   /**
    * Returns the not null check complied value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isNotNullCheckComplied(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_NOT_NULL_CHECK_COMPLIED));
   }
   
   /**
    * Returns the has not null check value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean hasNotNullCheck(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_HAS_NOT_NULL_CHECK));
   }
   
   /**
    * Returns the precondition complied value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isPreconditionComplied(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_PRECONDITION_COMPLIED));
   }
   
   /**
    * Returns the initially valid value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isInitiallyValid(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_INITIALLY_VALID));
   }
   
   /**
    * Returns the value string value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getValueString(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_VALUE_STRING);
   }
   
   /**
    * Returns the reference type name value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getReferenceTypeName(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_REFERENCE_TYPE_NAME);
   }
}
