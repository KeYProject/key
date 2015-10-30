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
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.resource.StringConverter;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.ISEValue;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.model.impl.AbstractSEBaseMethodReturn;
import org.key_project.sed.core.model.memory.ISEMemoryBaseMethodReturn;
import org.key_project.sed.core.model.memory.ISEMemoryNode;
import org.key_project.sed.core.model.memory.ISEMemoryGroupable;
import org.key_project.sed.core.model.memory.ISEMemoryStackFrameCompatibleDebugNode;
import org.key_project.sed.core.model.memory.SEMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEMemoryBranchStatement;
import org.key_project.sed.core.model.memory.SEMemoryConstraint;
import org.key_project.sed.core.model.memory.SEMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEMemoryExceptionalMethodReturn;
import org.key_project.sed.core.model.memory.SEMemoryExceptionalTermination;
import org.key_project.sed.core.model.memory.SEMemoryLoopBodyTermination;
import org.key_project.sed.core.model.memory.SEMemoryLoopCondition;
import org.key_project.sed.core.model.memory.SEMemoryLoopInvariant;
import org.key_project.sed.core.model.memory.SEMemoryLoopStatement;
import org.key_project.sed.core.model.memory.SEMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEMemoryMethodContract;
import org.key_project.sed.core.model.memory.SEMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEMemoryStatement;
import org.key_project.sed.core.model.memory.SEMemoryTermination;
import org.key_project.sed.core.model.memory.SEMemoryThread;
import org.key_project.sed.core.model.memory.SEMemoryValue;
import org.key_project.sed.core.model.memory.SEMemoryVariable;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * <p>
 * Instances of this class are used to read proprietary XML file
 * created via {@link SEXMLWriter}. The result is a {@link List} of
 * contained {@link ISEDebugTarget}s. The created instances are memory
 * instances and contains only the saved values. An execution at runtime, like
 * termination, step over, etc. is not possible.
 * </p>
 * <p>
 * The main use case of the serialization is to persistent an actual
 * {@link ISEDebugTarget} as oracle file which is later used in test cases
 * to compare a given {@link ISEDebugTarget} with the loaded instance
 * of the oracle file.
 * </p>
 * @author Martin Hentschel
 * @see SEXMLWriter
 */
public class SEXMLReader {
   /**
    * The {@link ILaunch} to use.
    */
   private final ILaunch launch;
   
   /**
    * Is this {@link ISEDebugTarget} executable meaning that
    * suspend, resume, step operations and disconnect are supported?;
    */
   private final boolean executable;   
   
   /**
    * Constructor.
    */
   public SEXMLReader() {
      this(null, false);
   }
   
   /**
    * Constructor.
    * @param launch The {@link ILaunch} to use.
    * @param executable {@code true} Support suspend, resume, etc.; {@code false} Do not support suspend, resume, etc.
    */
   public SEXMLReader(ILaunch launch, boolean executable) {
      this.launch = launch;
      this.executable = executable;
   }

   /**
    * Parses the given XML content.
    * @param xml The XML content to parse.
    * @return The contained {@link ISEDebugTarget}s in the given XML content.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public List<ISEDebugTarget> read(String xml) throws ParserConfigurationException, SAXException, IOException {
      return xml != null ? read(new ByteArrayInputStream(xml.getBytes())) : null;
   }
   
   /**
    * Parses the given XML content.
    * @param xml The XML content to parse.
    * @return The contained {@link ISEDebugTarget}s in the given XML content.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    * @throws CoreException Occurred Exception.
    */
   public List<ISEDebugTarget> read(IFile file) throws ParserConfigurationException, SAXException, IOException, CoreException {
      return file != null ? read(file.getContents()) : null;
   }
   
   /**
    * Parses the given XML content defined by the {@link InputStream}.
    * @param in The {@link InputStream} with the XML content to parse.
    * @return The contained {@link ISEDebugTarget}s in the given XML content.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public List<ISEDebugTarget> read(InputStream in) throws ParserConfigurationException, SAXException, IOException {
      if (in != null) {
         try {
            // Parse XML document
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setNamespaceAware(true);
            SAXParser saxParser = factory.newSAXParser();
            SEDSAXHandler handler = new SEDSAXHandler();
            saxParser.parse(in, handler);
            // Create call stacks
            Set<Entry<ISEMemoryNode, List<String>>> entries = handler.getCallStackEntriesMap().entrySet();
            for (Entry<ISEMemoryNode, List<String>> entry : entries) {
               List<ISENode> callStack = new LinkedList<ISENode>();
               for (String nodeRefId : entry.getValue()) {
                  ISEDebugElement element = handler.getElementById(nodeRefId);
                  if (element == null) {
                     throw new SAXException("Referenced node with ID \"" + nodeRefId + "\" is not available in model.");
                  }
                  if (!(element instanceof ISENode)) {
                     throw new SAXException("Referenced node with ID \"" + nodeRefId + "\" refers to wrong model object \"" + element + "\".");
                  }
                  callStack.add((ISENode)element);
               }
               entry.getKey().setCallStack(callStack.toArray(new ISENode[callStack.size()]));
            }
            // Set known terminations
            Set<Entry<SEMemoryThread, List<String>>> terminationEntries = handler.getTerminationEntriesMap().entrySet();
            for (Entry<SEMemoryThread, List<String>> entry : terminationEntries) {
               for (String nodeRefId : entry.getValue()) {
                  ISEDebugElement element = handler.getElementById(nodeRefId);
                  if (element == null) {
                     throw new SAXException("Referenced node with ID \"" + nodeRefId + "\" is not available in model.");
                  }
                  if (!(element instanceof ISETermination)) {
                     throw new SAXException("Referenced node with ID \"" + nodeRefId + "\" refers to wrong model object \"" + element + "\".");
                  }
                  entry.getKey().addTermination((ISETermination)element);
               }
            }
            // Set relevant constraints
            Set<Entry<SEMemoryValue, List<String>>> relevantConstraintEntries = handler.getRelevantConstraintsMap().entrySet();
            for (Entry<SEMemoryValue, List<String>> entry : relevantConstraintEntries) {
               for (String constraintRefId : entry.getValue()) {
                  ISEDebugElement element = handler.getElementById(constraintRefId);
                  if (element == null) {
                     throw new SAXException("Referenced constraint with ID \"" + constraintRefId + "\" is not available in model.");
                  }
                  if (!(element instanceof ISEConstraint)) {
                     throw new SAXException("Referenced constraint with ID \"" + constraintRefId + "\" refers to wrong model object \"" + element + "\".");
                  }
                  entry.getKey().addRelevantConstraint((ISEConstraint)element);
               }
            }
            // Inject child references
            Set<Entry<ISEMemoryNode, List<ChildReference>>> childReferences = handler.getNodeChildReferences().entrySet();
            for (Entry<ISEMemoryNode, List<ChildReference>> entry : childReferences) {
               for (ChildReference references : entry.getValue()) {
                  ISEDebugElement element = handler.getElementById(references.getId());
                  if (element == null) {
                     throw new SAXException("Referenced node with ID \"" + references.getId() + "\" is not available in model.");
                  }
                  if (!(element instanceof ISENode)) {
                     throw new SAXException("Referenced node with ID \"" + references.getId() + "\" refers to wrong model object \"" + element + "\".");
                  }
                  entry.getKey().addChild((ISENode)element);
               }
            }
            // Inject group start references
            Set<Entry<ISEMemoryNode, List<GroupEndReference>>> groupEndReferences = handler.getGroupEndReferences().entrySet();
            for (Entry<ISEMemoryNode, List<GroupEndReference>> entry : groupEndReferences) {
               for (GroupEndReference references : entry.getValue()) {
                  ISEDebugElement element = handler.getElementById(references.getId());
                  if (element == null) {
                     throw new SAXException("Referenced node with ID \"" + references.getId() + "\" is not available in model.");
                  }
                  if (!(element instanceof ISEBranchCondition)) {
                     throw new SAXException("Referenced node with ID \"" + references.getId() + "\" refers to wrong model object \"" + element + "\".");
                  }
                  entry.getKey().addGroupStartCondition((ISEBranchCondition)element);
               }
            }
            // Inject method return conditions
            Set<Entry<AbstractSEBaseMethodReturn, String>> returnConditions = handler.getMethodReturnConditionReferences().entrySet();
            for (Entry<AbstractSEBaseMethodReturn, String> entry : returnConditions) {
               ISEDebugElement element = handler.getElementById(entry.getValue());
               if (element == null) {
                  throw new SAXException("Referenced node with ID \"" + entry.getValue() + "\" is not available in model.");
               }
               if (!(element instanceof ISEBranchCondition)) {
                  throw new SAXException("Referenced node with ID \"" + entry.getValue() + "\" refers to wrong model object \"" + element + "\".");
               }
               if (entry.getKey() instanceof SEMemoryMethodReturn) {
                  ((SEMemoryMethodReturn) entry.getKey()).setMethodReturnCondition((ISEBranchCondition)element);
               }
               else if (entry.getKey() instanceof SEMemoryExceptionalMethodReturn) {
                  ((SEMemoryExceptionalMethodReturn) entry.getKey()).setMethodReturnCondition((ISEBranchCondition)element);
               }
               else {
                  throw new SAXException("Unsupported method return \"" + entry.getKey() + "\".");
               }
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
    * created via {@link SEXMLWriter}.
    * @author Martin Hentschel
    */
   private class SEDSAXHandler extends DefaultHandler {
      /**
       * The found {@link ISEDebugTarget}s.
       */
      private final List<ISEDebugTarget> result = new LinkedList<ISEDebugTarget>();
      
      /**
       * The current {@link SEMemoryDebugTarget}.
       */
      private SEMemoryDebugTarget target;
      
      /**
       * The current {@link SEMemoryThread}.
       */
      private SEMemoryThread thread;
      
      /**
       * The parent hierarchy filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private final Deque<ISEMemoryNode> parentStack = new LinkedList<ISEMemoryNode>();
      
      /**
       * The parent hierarchy of variables and values filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private final Deque<IDebugElement> variablesValueStack = new LinkedList<IDebugElement>();
      
      /**
       * Maps {@link ISEMemoryNode} to the IDs of their calls tacks.
       */
      private final Map<ISEMemoryNode, List<String>> callStackEntriesMap = new HashMap<ISEMemoryNode, List<String>>();
      
      /**
       * Maps {@link ISEThread} to the IDs of their known termination nodes.
       */
      private final Map<SEMemoryThread, List<String>> terminationEntriesMap = new HashMap<SEMemoryThread, List<String>>();

      /**
       * Maps the element ID ({@link ISEDebugElement#getId()}) to the its {@link ISEDebugElement} instance.
       */
      private final Map<String, ISEDebugElement> elementIdMapping = new HashMap<String, ISEDebugElement>();
      
      /**
       * Maps the annotation ID ({@link ISEAnnotation#getId()}) to the its {@link ISEAnnotation} instance.
       */
      private final Map<String, ISEAnnotation> annotationIdMapping = new HashMap<String, ISEAnnotation>();
      
      /**
       * Maps {@link ISEMemoryNode} to its child references.
       */
      private final Map<ISEMemoryNode, List<ChildReference>> nodeChildReferences = new HashMap<ISEMemoryNode, List<ChildReference>>();
      
      /**
       * Maps {@link ISEMemoryNode} to its group end references.
       */
      private final Map<ISEMemoryNode, List<GroupEndReference>> groupEndReferences = new HashMap<ISEMemoryNode, List<GroupEndReference>>();
      
      /**
       * Maps {@link AbstractSEBaseMethodReturn}s to their method return conditions.
       */
      private final Map<AbstractSEBaseMethodReturn, String> methodReturnConditionReferences = new HashMap<AbstractSEBaseMethodReturn, String>();
      
      /**
       * Maps {@link SEMemoryValue}d to the IDs of their relevant constraints.
       */
      private Map<SEMemoryValue, List<String>> relevantConstraintsMap = new HashMap<SEMemoryValue, List<String>>();
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         ISEMemoryNode parent = parentStack.peekFirst();
         IDebugElement parentVariableOrValue = variablesValueStack.peekFirst();
         if (isCallStackEntry(uri, localName, qName)) {
            List<String> callStack = callStackEntriesMap.get(parent);
            if (callStack == null) {
               callStack = new LinkedList<String>();
               callStackEntriesMap.put(parent, callStack);
            }
            callStack.add(getNodeIdRef(attributes));
         }
         else if (isRelevantConstraint(uri, localName, qName)) {
            if (parentVariableOrValue instanceof SEMemoryValue) {
               List<String> entriesList = relevantConstraintsMap.get((SEMemoryValue)parentVariableOrValue);
               if (entriesList == null) {
                  entriesList = new LinkedList<String>();
                  relevantConstraintsMap.put((SEMemoryValue)parentVariableOrValue, entriesList);
               }
               entriesList.add(getConstraintIdRef(attributes));
            }
            else {
               throw new SAXException("Can't add relevant constraint to parent.");
            }
         }
         else if (isTerminationEntry(uri, localName, qName)) {
            if (parent == null) {
               List<String> entriesList = terminationEntriesMap.get(thread);
               if (entriesList == null) {
                  entriesList = new LinkedList<String>();
                  terminationEntriesMap.put(thread, entriesList);
               }
               entriesList.add(getNodeIdRef(attributes));
            }
            else {
               throw new SAXException("Can't add termination entry to parent.");
            }
         }
         else if (isCallStateVariable(uri, localName, qName)) {
            IVariable variable = createVariable(target, (IStackFrame)parent, uri, localName, qName, attributes);
            if (variablesValueStack.isEmpty()) {
               if (parent instanceof ISEMemoryBaseMethodReturn) {
                  ((ISEMemoryBaseMethodReturn)parent).addCallStateVariable(variable);
                  variablesValueStack.addFirst(variable);
               }
               else {
                  throw new SAXException("Can't add call state variable to parent.");
               }
            }
            else {
               throw new SAXException("Can't add call state variable to parent.");
            }
         }
         else {
            Object obj = createElement(target, parent != null ? parent : thread, thread, parentVariableOrValue, uri, localName, qName, attributes, annotationIdMapping, methodReturnConditionReferences);
            if (obj instanceof ISEDebugElement) {
               ISEDebugElement element = (ISEDebugElement)obj;
               elementIdMapping.put(element.getId(), element);
            }
            if (obj instanceof ChildReference) {
               List<ChildReference> refs = nodeChildReferences.get(parent);
               if (refs == null) {
                  refs = new LinkedList<ChildReference>();
                  nodeChildReferences.put(parent, refs);
               }
               refs.add((ChildReference)obj);
            }
            else if (obj instanceof GroupEndReference) {
               List<GroupEndReference> refs = groupEndReferences.get(parent);
               if (refs == null) {
                  refs = new LinkedList<GroupEndReference>();
                  groupEndReferences.put(parent, refs);
               }
               refs.add((GroupEndReference)obj);
            }
            else if (obj instanceof SEMemoryDebugTarget) {
               target = (SEMemoryDebugTarget)obj;
               result.add(target);
            }
            else if (obj instanceof ISEConstraint) {
               if (parent != null) {
                  parent.addConstraint((ISEConstraint) obj);
               }
               else {
                  thread.addConstraint((ISEConstraint) obj);
               }
            }
            else if (obj instanceof IVariable) {
               IVariable variable = (IVariable)obj;
               if (variablesValueStack.isEmpty()) {
                  if (parent instanceof ISEMemoryStackFrameCompatibleDebugNode) {
                     ((ISEMemoryStackFrameCompatibleDebugNode)parent).addVariable(variable);
                  }
                  else if (parent == null && thread != null) {
                     thread.addVariable(variable);
                  }
                  else {
                     throw new SAXException("Can't add variable to parent.");
                  }
               }
               else {
                  if (parentVariableOrValue instanceof SEMemoryValue) {
                     ((SEMemoryValue)parentVariableOrValue).addVariable(variable);
                  }
                  else {
                     throw new SAXException("Can't add variable to parent.");
                  }
               }
               variablesValueStack.addFirst(variable);
            }
            else if (obj instanceof IValue) {
               IValue value = (IValue)obj;
               if (parentVariableOrValue instanceof SEMemoryVariable) {
                  ((SEMemoryVariable)parentVariableOrValue).setValue(value);
               }
               else {
                  throw new SAXException("Can't add value to parent.");
               }
               variablesValueStack.addFirst(value);
            }
            else if (obj instanceof SEMemoryThread) {
               thread = (SEMemoryThread)obj;
               if (target != null) {
                  target.addSymbolicThread(thread);
               }
               else {
                  throw new SAXException("Model is in inconsistent state.");
               }
            }
            else if (obj instanceof ISEMemoryNode) {
               ISEMemoryNode child = (ISEMemoryNode)obj; 
               parentStack.addFirst(child);
               if (isMethodReturnCondition(uri, localName, qName)) {
                  ((SEMemoryMethodCall)parent).addMethodReturnCondition((ISEBranchCondition)child);
               }
               else if (isGroupEndCondition(uri, localName, qName)) {
                  ((ISEMemoryGroupable)parent).addGroupEndCondition((ISEBranchCondition)child);
               }
               else {
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
            else if (obj instanceof ISEAnnotation) {
               ISEAnnotation annotation = (ISEAnnotation)obj;
               annotationIdMapping.put(annotation.getId(), annotation);
               target.registerAnnotation(annotation);
            }
            else if (obj instanceof ISEAnnotationLink) {
               ISEAnnotationLink link = (ISEAnnotationLink)obj;
               link.getSource().addLink(link);
            }
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (isCallStateVariable(uri, localName, qName) || 
             isVariable(uri, localName, qName) || 
             isValue(uri, localName, qName)) {
            variablesValueStack.removeFirst();
         }
         else if (isConstraint(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isRelevantConstraint(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isCallStackEntry(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isTerminationEntry(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isAnnotation(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isAnnotationLink(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isAnnotationLink(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isChildReferences(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isGroupEndConditionReference(uri, localName, qName)) {
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
            else if (SEXMLWriter.TAG_LAUNCH.equals(qName)) {
               // Nothing to do, but still valid.
            }
            else {
               throw new SAXException("Model is in inconsistent state.");
            }
         }
      }

      /**
       * Returns the found {@link ISEDebugTarget}s.
       * @return The found {@link ISEDebugTarget}s.
       */
      public List<ISEDebugTarget> getResult() {
         return result;
      }

      /**
       * Returns the mapping of {@link ISENode}s to their call stacks.
       * @return The mapping of {@link ISENode}s to their call stacks.
       */
      public Map<ISEMemoryNode, List<String>> getCallStackEntriesMap() {
         return callStackEntriesMap;
      }

      /**
       * Returns the mapping of {@link SEMemoryThread}s to their call stacks.
       * @return The mapping of {@link SEMemoryThread}s to their call stacks.
       */
      public Map<SEMemoryThread, List<String>> getTerminationEntriesMap() {
         return terminationEntriesMap;
      }

      /**
       * Returns the mapping of {@link SEMemoryValue}s to their relevant constraints.
       * @return The mapping of {@link SEMemoryValue}s to their relevant constraints.
       */
      public Map<SEMemoryValue, List<String>> getRelevantConstraintsMap() {
         return relevantConstraintsMap;
      }

      /**
       * Returns the node child references.
       * @return The node child references.
       */
      public Map<ISEMemoryNode, List<ChildReference>> getNodeChildReferences() {
         return nodeChildReferences;
      }

      /**
       * Returns the group end references.
       * @return The group end references.
       */
      public Map<ISEMemoryNode, List<GroupEndReference>> getGroupEndReferences() {
         return groupEndReferences;
      }

      /**
       * Returns the method return conditions.
       * @return The method return conditions.
       */
      public Map<AbstractSEBaseMethodReturn, String> getMethodReturnConditionReferences() {
         return methodReturnConditionReferences;
      }

      /**
       * Returns the instantiated {@link ISEDebugElement} with the give ID.
       * @param id The ID.
       * @return The instantiated {@link ISEDebugElement} or {@code null} if not available.
       */
      public ISEDebugElement getElementById(String id) {
         return elementIdMapping.get(id);
      }
   }
   
   /**
    * Checks if the given tag name represents a constraint.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents a constraint, {@code false} represents something else.
    */
   protected boolean isConstraint(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_CONSTRAINT.equals(qName);
   }

   /**
    * Checks if the given tag name represents a relevant constraint.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents a constraint, {@code false} represents something else.
    */
   protected boolean isRelevantConstraint(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_RELEVANT_CONSTRAINT.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents a call stack entry.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents a call stack entry, {@code false} represents something else.
    */
   protected boolean isCallStackEntry(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_CALL_STACK_ENTRY.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents a termination entry.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents a termination entry, {@code false} represents something else.
    */
   protected boolean isTerminationEntry(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_TERMINATION_ENTRY.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link ISEAnnotation}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link ISEAnnotation}, {@code false} represents something else.
    */
   protected boolean isAnnotation(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_ANNOTATION.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link ISEAnnotationLink}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link ISEAnnotationLink}, {@code false} represents something else.
    */
   protected boolean isAnnotationLink(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_ANNOTATION_LINK.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents a {@link ChildReference}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link ChildReference}, {@code false} represents something else.
    */
   protected boolean isChildReferences(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_CHILD_REFERENCE.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link ISEBranchCondition}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link ISEBranchCondition}, {@code false} represents something else.
    */
   protected boolean isGroupEndCondition(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_GROUP_END_CONDITION.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link ISEBranchCondition}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link ISEBranchCondition}, {@code false} represents something else.
    */
   protected boolean isMethodReturnCondition(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_METHOD_RETURN_CONDITIONS.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents a {@link GroupEndReference}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents a {@link GroupEndReference}, {@code false} represents something else.
    */
   protected boolean isGroupEndConditionReference(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_GROUP_END_CONDITION_REFERENCE.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link IVariable}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link IVariable}, {@code false} represents something else.
    */
   protected boolean isCallStateVariable(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_CALL_STATE_VARIABLE.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link IVariable}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link IVariable}, {@code false} represents something else.
    */
   protected boolean isVariable(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_VARIABLE.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link IValue}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link IValue}, {@code false} represents something else.
    */
   protected boolean isValue(String uri, String localName, String qName) {
      return SEXMLWriter.TAG_VALUE.equals(qName);
   }
   
   /**
    * Creates an {@link Object} for the element defined by the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param parentVariableOrValue The parent {@link ISEVariable} / {@link ISEValue} if available or {@code null} otherwise.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @param methodReturnConditionReferences The method return conditions.
    * @return The created {@link Object}.
    * @throws SAXException Occurred Exception.
    */
   protected Object createElement(ISEDebugTarget target, ISENode parent, ISEThread thread, IDebugElement parentVariableOrValue, String uri, String localName, String qName, Attributes attributes, Map<String, ISEAnnotation> annotationIdMapping, Map<AbstractSEBaseMethodReturn, String> methodReturnConditionReferences) throws SAXException {
      if (SEXMLWriter.TAG_LAUNCH.equals(qName)) {
         return null; // Nothing to do
      }
      else if (SEXMLWriter.TAG_CHILD_REFERENCE.equals(qName)) {
         return new ChildReference(getNodeIdRef(attributes));
      }
      else if (SEXMLWriter.TAG_GROUP_END_CONDITION_REFERENCE.equals(qName)) {
         return new GroupEndReference(getNodeIdRef(attributes));
      }
      else if (SEXMLWriter.TAG_DEBUG_TARGET.equals(qName)) {
         return createDebugTarget(uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_BRANCH_CONDITION.equals(qName) ||
               SEXMLWriter.TAG_METHOD_RETURN_CONDITIONS.equals(qName) ||
               SEXMLWriter.TAG_GROUP_END_CONDITION.equals(qName)) {
         return createBranchCondition(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_BRANCH_STATEMENT.equals(qName)) {
         return createBranchStatement(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_EXCEPTIONAL_TERMINATION.equals(qName)) {
         return createExceptionalTermination(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_LOOP_BODY_TERMINATION.equals(qName)) {
         return createLoopBodyTermination(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_LOOP_CONDITION.equals(qName)) {
         return createLoopCondition(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_LOOP_STATEMENT.equals(qName)) {
         return createLoopStatement(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_METHOD_CALL.equals(qName)) {
         return createMethodCall(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_METHOD_RETURN.equals(qName)) {
         return createMethodReturn(target, parent, thread, uri, localName, qName, attributes, methodReturnConditionReferences);
      }
      else if (SEXMLWriter.TAG_EXCEPTIONAL_METHOD_RETURN.equals(qName)) {
         return createExceptionalMethodReturn(target, parent, thread, uri, localName, qName, attributes, methodReturnConditionReferences);
      }
      else if (SEXMLWriter.TAG_STATEMENT.equals(qName)) {
         return createStatement(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_TERMINATION.equals(qName)) {
         return createTermination(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_THREAD.equals(qName)) {
         return createThread(target, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_VARIABLE.equals(qName)) {
         return createVariable(target, (IStackFrame)parent, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_VALUE.equals(qName)) {
         return createValue(target, (ISEVariable)parentVariableOrValue, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_METHOD_CONTRACT.equals(qName)) {
         return createMethodContract(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_LOOP_INVARIANT.equals(qName)) {
         return createLoopInvariant(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_ANNOTATION.equals(qName)) {
         return createAnnotation(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEXMLWriter.TAG_ANNOTATION_LINK.equals(qName)) {
         return createAnnotationLink(target, parent, thread, uri, localName, qName, attributes, annotationIdMapping);
      }
      else if (SEXMLWriter.TAG_CONSTRAINT.equals(qName)) {
         return createConstraint(target, parent, thread, uri, localName, qName, attributes);
      }
      else {
         throw new SAXException("Unknown tag \"" + qName + "\".");
      }
   }
   
   protected SEMemoryConstraint createConstraint(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryConstraint constraint = new SEMemoryConstraint(target, getName(attributes));
      constraint.setId(getId(attributes));
      return constraint;
   }

   protected ISEAnnotationLink createAnnotationLink(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes, Map<String, ISEAnnotation> annotationIdMapping) throws SAXException {
      String sourceId = getAnnotationLinkSource(attributes);
      String targetId = getAnnotationLinkTarget(attributes);
      if (!ObjectUtil.equals(targetId, parent.getId())) {
         throw new SAXException("Annotation link is contained in wrong node.");
      }
      ISEAnnotation annotation = annotationIdMapping.get(sourceId);
      if (annotation == null) {
         throw new SAXException("Annotation with ID \"" + sourceId + "\" is not available.");
      }
      ISEAnnotationLink link = annotation.getType().createLink(annotation, parent);
      link.setId(getId(attributes));
      String content = getAnnotationContent(attributes);
      if (content != null) {
         annotation.getType().restoreAnnotationLink(link, content);
      }
      return link;
   }
   
   protected ISEAnnotation createAnnotation(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      String typeId = getTypeId(attributes);
      ISEAnnotationType type = SEAnnotationUtil.getAnnotationtype(typeId);
      if (type == null) {
         throw new SAXException("Annotation type with type ID \"" + typeId + "\" does not exit.");
      }
      ISEAnnotation annotation = type.createAnnotation();
      annotation.setId(getId(attributes));
      annotation.setEnabled(isEnabled(attributes));
      boolean highlightBackground = isHighlightBackground(attributes);
      RGB backgroundColor = getBackgroundColor(attributes);
      boolean highlightForeground = isHighlightForeground(attributes);
      RGB foregroundColor = getForegroundColor(attributes);
      if (annotation.isHighlightBackground() != highlightBackground) {
         annotation.setCustomHighlightBackground(highlightBackground);
      }
      if (!ObjectUtil.equals(annotation.getBackgroundColor(), backgroundColor)) {
         annotation.setCustomBackgroundColor(backgroundColor);
      }
      if (annotation.isHighlightForeground() != highlightForeground) {
         annotation.setCustomHighlightForeground(highlightForeground);
      }
      if (!ObjectUtil.equals(annotation.getForegroundColor(), foregroundColor)) {
         annotation.setCustomForegroundColor(foregroundColor);
      }
      String content = getAnnotationContent(attributes);
      if (content != null) {
         type.restoreAnnotation(annotation, content);
      }
      return annotation;
   }

   protected SEMemoryValue createValue(ISEDebugTarget target, ISEVariable parent, String uri, String localName, String qName, Attributes attributes) {
      SEMemoryValue value = new SEMemoryValue(target, parent);
      value.setId(getId(attributes));
      value.setAllocated(isAllocated(attributes));
      value.setReferenceTypeName(getReferenceTypeName(attributes));
      value.setValueString(getValueString(attributes));
      value.setMultiValued(isMultiValued(attributes));
      return value;
   }
   
   protected SEMemoryVariable createVariable(ISEDebugTarget target, IStackFrame stackFrame, String uri, String localName, String qName, Attributes attributes) {
      SEMemoryVariable variable = new SEMemoryVariable(target, stackFrame);
      variable.setId(getId(attributes));
      variable.setName(getName(attributes));
      variable.setReferenceTypeName(getReferenceTypeName(attributes));
      return variable;
   }
   
   /**
    * Creates a {@link SEMemoryBranchCondition} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryBranchCondition}.
    */
   protected SEMemoryBranchCondition createBranchCondition(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) {
      SEMemoryBranchCondition branchCondition = new SEMemoryBranchCondition(target, parent, thread);
      fillDebugNode(branchCondition, attributes);
      return branchCondition;
   }
   
   /**
    * Creates a {@link SEMemoryDebugTarget} instance for the content in the given tag.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryDebugTarget}.
    */
   protected SEMemoryDebugTarget createDebugTarget(String uri, String localName, String qName, Attributes attributes) {
      SEMemoryDebugTarget target = new SEMemoryDebugTarget(launch, executable);
      target.setId(getId(attributes));
      target.setName(getName(attributes));
      target.setModelIdentifier(getModelIdentifier(attributes));
      return target;
   }

   /**
    * Creates a {@link SEMemoryBranchStatement} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryBranchStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryBranchStatement createBranchStatement(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryBranchStatement branchStatement = new SEMemoryBranchStatement(target, parent, thread);
      branchStatement.setSourcePath(getSourcePath(attributes));
      fillDebugNode(branchStatement, attributes);
      fillStackFrame(branchStatement, attributes);
      return branchStatement;
   }

   /**
    * Creates a {@link SEMemoryExceptionalTermination} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryExceptionalTermination}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryExceptionalTermination createExceptionalTermination(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryExceptionalTermination termination = new SEMemoryExceptionalTermination(target, parent, thread, isVerified(attributes));
      fillDebugNode(termination, attributes);
      fillStackFrame(termination, attributes);
      return termination;
   }
   
   /**
    * Creates a {@link SEMemoryLoopBodyTermination} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryLoopBodyTermination}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryLoopBodyTermination createLoopBodyTermination(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryLoopBodyTermination termination = new SEMemoryLoopBodyTermination(target, parent, thread, isVerified(attributes));
      fillDebugNode(termination, attributes);
      fillStackFrame(termination, attributes);
      return termination;
   }
   
   /**
    * Creates a {@link SEMemoryLoopCondition} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryLoopCondition}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryLoopCondition createLoopCondition(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryLoopCondition loopCondition = new SEMemoryLoopCondition(target, parent, thread);
      loopCondition.setSourcePath(getSourcePath(attributes));
      fillDebugNode(loopCondition, attributes);
      fillStackFrame(loopCondition, attributes);
      return loopCondition;
   }
   
   /**
    * Creates a {@link SEMemoryLoopStatement} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryLoopStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryLoopStatement createLoopStatement(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryLoopStatement loopStatement = new SEMemoryLoopStatement(target, parent, thread);
      loopStatement.setSourcePath(getSourcePath(attributes));
      fillDebugNode(loopStatement, attributes);
      fillStackFrame(loopStatement, attributes);
      return loopStatement;
   }
   
   /**
    * Creates a {@link SEMemoryMethodCall} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryMethodCall}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryMethodCall createMethodCall(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryMethodCall methodCall = new SEMemoryMethodCall(target, parent, thread);
      methodCall.setSourcePath(getSourcePath(attributes));
      fillDebugNode(methodCall, attributes);
      fillStackFrame(methodCall, attributes);
      return methodCall;
   }
   
   /**
    * Creates a {@link SEMemoryMethodReturn} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryMethodReturn}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryMethodReturn createMethodReturn(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes, Map<AbstractSEBaseMethodReturn, String> methodReturnConditionReferences) throws SAXException {
      SEMemoryMethodReturn methodReturn = new SEMemoryMethodReturn(target, parent, thread);
      methodReturn.setSourcePath(getSourcePath(attributes));
      fillDebugNode(methodReturn, attributes);
      fillStackFrame(methodReturn, attributes);
      String methodReturnCondition = getMethodReturnCondition(attributes);
      if (!StringUtil.isEmpty(methodReturnCondition)) {
         methodReturnConditionReferences.put(methodReturn, methodReturnCondition);
      }
      return methodReturn;
   }
   
   /**
    * Creates a {@link SEMemoryExceptionalMethodReturn} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryExceptionalMethodReturn}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryExceptionalMethodReturn createExceptionalMethodReturn(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes, Map<AbstractSEBaseMethodReturn, String> methodReturnConditionReferences) throws SAXException {
      SEMemoryExceptionalMethodReturn methodReturn = new SEMemoryExceptionalMethodReturn(target, parent, thread);
      methodReturn.setSourcePath(getSourcePath(attributes));
      fillDebugNode(methodReturn, attributes);
      fillStackFrame(methodReturn, attributes);
      String methodReturnCondition = getMethodReturnCondition(attributes);
      if (!StringUtil.isEmpty(methodReturnCondition)) {
         methodReturnConditionReferences.put(methodReturn, methodReturnCondition);
      }
      return methodReturn;
   }

   /**
    * Creates a {@link SEMemoryStatement} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryStatement createStatement(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryStatement statement = new SEMemoryStatement(target, parent, thread);
      statement.setSourcePath(getSourcePath(attributes));
      fillDebugNode(statement, attributes);
      fillStackFrame(statement, attributes);
      return statement;
   }
   
   /**
    * Creates a {@link SEMemoryMethodContract} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryMethodContract createMethodContract(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryMethodContract methodContract = new SEMemoryMethodContract(target, parent, thread);
      methodContract.setSourcePath(getSourcePath(attributes));
      fillDebugNode(methodContract, attributes);
      fillStackFrame(methodContract, attributes);
      methodContract.setPreconditionComplied(isPreconditionComplied(attributes));
      methodContract.setHasNotNullCheck(hasNotNullCheck(attributes));
      methodContract.setNotNullCheckComplied(isNotNullCheckComplied(attributes));
      return methodContract;
   }
   
   /**
    * Creates a {@link SEMemoryLoopInvariant} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryLoopInvariant createLoopInvariant(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryLoopInvariant loopInvariant = new SEMemoryLoopInvariant(target, parent, thread);
      loopInvariant.setSourcePath(getSourcePath(attributes));
      fillDebugNode(loopInvariant, attributes);
      fillStackFrame(loopInvariant, attributes);
      loopInvariant.setInitiallyValid(isInitiallyValid(attributes));
      return loopInvariant;
   }
   
   /**
    * Creates a {@link SEMemoryTermination} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISENode} or {@code null} if not available.
    * @param thread The parent {@link ISEThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryTermination}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEMemoryTermination createTermination(ISEDebugTarget target, ISENode parent, ISEThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEMemoryTermination termination = new SEMemoryTermination(target, parent, thread, isVerified(attributes));
      fillDebugNode(termination, attributes);
      fillStackFrame(termination, attributes);
      return termination;
   }
   
   /**
    * Creates a {@link SEMemoryThread} instance for the content in the given tag.
    * @param target The parent {@link ISEDebugTarget} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEMemoryThread}.
    */   
   protected SEMemoryThread createThread(ISEDebugTarget target, String uri, String localName, String qName, Attributes attributes) {
      SEMemoryThread thread = new SEMemoryThread(target, executable);
      fillDebugNode(thread, attributes);
      return thread;
   }
   
   /**
    * Fills the attributes of the given {@link ISEMemoryNode}.
    * @param node The {@link ISEMemoryNode} to fill.
    * @param attributes The {@link Attributes} which provides the content.
    */
   protected void fillDebugNode(ISEMemoryNode node, Attributes attributes) {
      node.setId(getId(attributes));
      node.setName(getName(attributes));
      node.setPathCondition(getPathCondition(attributes));
      if (node instanceof ISEMemoryGroupable) {
         ((ISEMemoryGroupable) node).setGroupable(isGroupable(attributes));
      }
   }

   /**
    * Fills the attributes of the given {@link ISEMemoryStackFrameCompatibleDebugNode}.
    * @param node The {@link ISEMemoryStackFrameCompatibleDebugNode} to fill.
    * @param attributes The {@link Attributes} which provides the content.
    * @throws SAXException Occurred Exception.
    */
   protected void fillStackFrame(ISEMemoryStackFrameCompatibleDebugNode node, Attributes attributes) throws SAXException {
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
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_ID);
   }
   
   /**
    * Returns the node id reference value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getNodeIdRef(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_NODE_ID_REF);
   }
   
   /**
    * Returns the constraint id reference value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getConstraintIdRef(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_CONSTRAINT_ID_REF);
   }
   
   /**
    * Returns the name value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getName(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_NAME);
   }

   /**
    * Returns the path condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getPathCondition(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_PATH_CONDITION);
   }
   
   /**
    * Returns the source path value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getSourcePath(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_SOURCE_PATH);
   }
   
   /**
    * Returns the method return condition ID.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getMethodReturnCondition(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_METHOD_RETURN_CONDITION);
   }
   
   /**
    * Returns the model identifier value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getModelIdentifier(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_MODEL_IDENTIFIER);
   }
   
   /**
    * Returns the line number value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    * @throws SAXException Occurred Exception.
    */
   protected int getLineNumber(Attributes attributes) throws SAXException {
      try {
         String value = attributes.getValue(SEXMLWriter.ATTRIBUTE_LINE_NUMBER);
         if (value != null) {
            return Integer.parseInt(value);
         }
         else {
            return -1;
         }
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
         String value = attributes.getValue(SEXMLWriter.ATTRIBUTE_CHAR_START);
         if (value != null) {
            return Integer.parseInt(value);
         }
         else {
            return -1;
         }
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
         String value = attributes.getValue(SEXMLWriter.ATTRIBUTE_CHAR_END);
         if (value != null) {
            return Integer.parseInt(value);
         }
         else {
            return -1;
         }
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
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_MULTI_VALUED));
   }
   
   /**
    * Returns the allocated value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isAllocated(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_ALLOCATED));
   }
   
   /**
    * Returns the verified value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isVerified(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_VERIFIED));
   }
   
   /**
    * Returns the not null check complied value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isNotNullCheckComplied(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_NOT_NULL_CHECK_COMPLIED));
   }
   
   /**
    * Returns the has not null check value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean hasNotNullCheck(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_HAS_NOT_NULL_CHECK));
   }
   
   /**
    * Returns the precondition complied value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isPreconditionComplied(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_PRECONDITION_COMPLIED));
   }
   
   /**
    * Returns the initially valid value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isInitiallyValid(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_INITIALLY_VALID));
   }
   
   /**
    * Returns the groupable value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isGroupable(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_GROUPABLE));
   }
   
   /**
    * Returns the value string value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getValueString(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_VALUE_STRING);
   }
   
   /**
    * Returns the reference type name value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getReferenceTypeName(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_REFERENCE_TYPE_NAME);
   }
   
   /**
    * Returns the type ID value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getTypeId(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_TYPE_ID);
   }
   
   /**
    * Returns the annotation content value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getAnnotationContent(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_CONTENT);
   }
   
   /**
    * Returns the enabled value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isEnabled(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_ENABLED));
   }
   
   /**
    * Returns the highlight background value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isHighlightBackground(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_HIGHLIGHT_BACKGROUND));
   }
   
   /**
    * Returns the highlight foreground value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isHighlightForeground(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEXMLWriter.ATTRIBUTE_HIGHLIGHT_FOREGROUND));
   }
   
   /**
    * Returns the background color value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected RGB getBackgroundColor(Attributes attributes) {
      return StringConverter.asRGB(attributes.getValue(SEXMLWriter.ATTRIBUTE_BACKGROUND_COLOR));
   }
   
   /**
    * Returns the foreground color value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected RGB getForegroundColor(Attributes attributes) {
      return StringConverter.asRGB(attributes.getValue(SEXMLWriter.ATTRIBUTE_FOREGROUND_COLOR));
   }
   
   /**
    * Returns the annotation link source value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getAnnotationLinkSource(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_ANNOTATION_LINK_SOURCE);
   }
   
   /**
    * Returns the annotation link target value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getAnnotationLinkTarget(Attributes attributes) {
      return attributes.getValue(SEXMLWriter.ATTRIBUTE_ANNOTATION_LINK_TARGET);
   }

   /**
    * Represents temporary a child reference.
    * @author Martin Hentschel
    */
   protected static class ChildReference {
      /**
       * The target ID.
       */
      private final String id;

      /**
       * Constructor.
       * @param id The target ID.
       */
      public ChildReference(String id) {
         this.id = id;
      }

      /**
       * Returns the target ID.
       * @return The target ID.
       */
      public String getId() {
         return id;
      }
   }

   /**
    * Represents temporary a group end reference.
    * @author Martin Hentschel
    */
   protected static class GroupEndReference {
      /**
       * The target ID.
       */
      private final String id;

      /**
       * Constructor.
       * @param id The target ID.
       */
      public GroupEndReference(String id) {
         this.id = id;
      }

      /**
       * Returns the target ID.
       * @return The target ID.
       */
      public String getId() {
         return id;
      }
   }
}