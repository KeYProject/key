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
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.resource.StringConverter;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.ISEDMemoryStackFrameCompatibleDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchStatement;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;
import org.key_project.sed.core.model.memory.SEDMemoryLoopBodyTermination;
import org.key_project.sed.core.model.memory.SEDMemoryLoopCondition;
import org.key_project.sed.core.model.memory.SEDMemoryLoopInvariant;
import org.key_project.sed.core.model.memory.SEDMemoryLoopStatement;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodContract;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.core.model.memory.SEDMemoryValue;
import org.key_project.sed.core.model.memory.SEDMemoryVariable;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.util.java.ObjectUtil;
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
    * The {@link ILaunch} to use.
    */
   private final ILaunch launch;
   
   /**
    * Is this {@link ISEDDebugTarget} executable meaning that
    * suspend, resume, step operations and disconnect are supported?;
    */
   private final boolean executable;   
   
   /**
    * Constructor.
    */
   public SEDXMLReader() {
      this(null, false);
   }
   
   /**
    * Constructor.
    * @param launch The {@link ILaunch} to use.
    * @param executable {@code true} Support suspend, resume, etc.; {@code false} Do not support suspend, resume, etc.
    */
   public SEDXMLReader(ILaunch launch, boolean executable) {
      this.launch = launch;
      this.executable = executable;
   }

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
       * Maps the annotation ID ({@link ISEDAnnotation#getId()}) to the its {@link ISEDAnnotation} instance.
       */
      private Map<String, ISEDAnnotation> annotationIdMapping = new HashMap<String, ISEDAnnotation>();
      
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
            Object obj = createElement(target, parent != null ? parent : thread, thread, uri, localName, qName, attributes, annotationIdMapping);
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
            else if (obj instanceof ISEDAnnotation) {
               ISEDAnnotation annotation = (ISEDAnnotation)obj;
               annotationIdMapping.put(annotation.getId(), annotation);
               target.registerAnnotation(annotation);
            }
            else if (obj instanceof ISEDAnnotationLink) {
               ISEDAnnotationLink link = (ISEDAnnotationLink)obj;
               link.getSource().addLink(link);
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
         else if (isAnnotation(uri, localName, qName)) {
            // Nothing to do
         }
         else if (isAnnotationLink(uri, localName, qName)) {
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
    * Checks if the given tag name represents an {@link ISEDAnnotation}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link ISEDAnnotation}, {@code false} represents something else.
    */
   protected boolean isAnnotation(String uri, String localName, String qName) {
      return SEDXMLWriter.TAG_ANNOTATION.equals(qName);
   }
   
   /**
    * Checks if the given tag name represents an {@link ISEDAnnotationLink}.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @return {@code true} represents an {@link ISEDAnnotationLink}, {@code false} represents something else.
    */
   protected boolean isAnnotationLink(String uri, String localName, String qName) {
      return SEDXMLWriter.TAG_ANNOTATION_LINK.equals(qName);
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
   protected Object createElement(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes, Map<String, ISEDAnnotation> annotationIdMapping) throws SAXException {
      if (SEDXMLWriter.TAG_LAUNCH.equals(qName)) {
         return null; // Nothing to do
      }
      else if (SEDXMLWriter.TAG_DEBUG_TARGET.equals(qName)) {
         return createDebugTarget(uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_BRANCH_CONDITION.equals(qName)) {
         return createBranchCondition(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_BRANCH_STATEMENT.equals(qName)) {
         return createBranchStatement(target, parent, thread, uri, localName, qName, attributes);
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
      else if (SEDXMLWriter.TAG_LOOP_STATEMENT.equals(qName)) {
         return createLoopStatement(target, parent, thread, uri, localName, qName, attributes);
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
      else if (SEDXMLWriter.TAG_METHOD_CONTRACT.equals(qName)) {
         return createMethodContract(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_LOOP_INVARIANT.equals(qName)) {
         return createLoopInvariant(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_ANNOTATION.equals(qName)) {
         return createAnnotation(target, parent, thread, uri, localName, qName, attributes);
      }
      else if (SEDXMLWriter.TAG_ANNOTATION_LINK.equals(qName)) {
         return createAnnotationLink(target, parent, thread, uri, localName, qName, attributes, annotationIdMapping);
      }
      else {
         throw new SAXException("Unknown tag \"" + qName + "\".");
      }
   }
   
   protected ISEDAnnotationLink createAnnotationLink(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes, Map<String, ISEDAnnotation> annotationIdMapping) throws SAXException {
      String sourceId = getAnnotationLinkSource(attributes);
      String targetId = getAnnotationLinkTarget(attributes);
      if (!ObjectUtil.equals(targetId, parent.getId())) {
         throw new SAXException("Annotation link is contained in wrong node.");
      }
      ISEDAnnotation annotation = annotationIdMapping.get(sourceId);
      if (annotation == null) {
         throw new SAXException("Annotation with ID \"" + sourceId + "\" is not available.");
      }
      ISEDAnnotationLink link = annotation.getType().createLink(annotation, parent);
      link.setId(getId(attributes));
      String content = getAnnotationContent(attributes);
      if (content != null) {
         annotation.getType().restoreAnnotationLink(link, content);
      }
      return link;
   }
   
   protected ISEDAnnotation createAnnotation(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      String typeId = getTypeId(attributes);
      ISEDAnnotationType type = SEDAnnotationUtil.getAnnotationtype(typeId);
      if (type == null) {
         throw new SAXException("Annotation type with type ID \"" + typeId + "\" does not exit.");
      }
      ISEDAnnotation annotation = type.createAnnotation();
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
      SEDMemoryBranchCondition branchCondition = new SEDMemoryBranchCondition(target, parent, thread);
      fillDebugNode(branchCondition, attributes);
      return branchCondition;
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
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(launch, executable);
      target.setId(getId(attributes));
      target.setName(getName(attributes));
      target.setModelIdentifier(getModelIdentifier(attributes));
      return target;
   }

   /**
    * Creates a {@link SEDMemoryBranchStatement} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryBranchStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryBranchStatement createBranchStatement(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryBranchStatement branchStatement = new SEDMemoryBranchStatement(target, parent, thread);
      branchStatement.setSourcePath(getSourcePath(attributes));
      fillDebugNode(branchStatement, attributes);
      fillStackFrame(branchStatement, attributes);
      return branchStatement;
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
      SEDMemoryExceptionalTermination termination = new SEDMemoryExceptionalTermination(target, parent, thread, isVerified(attributes));
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
      SEDMemoryLoopBodyTermination termination = new SEDMemoryLoopBodyTermination(target, parent, thread, isVerified(attributes));
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
      SEDMemoryLoopCondition loopCondition = new SEDMemoryLoopCondition(target, parent, thread);
      loopCondition.setSourcePath(getSourcePath(attributes));
      fillDebugNode(loopCondition, attributes);
      fillStackFrame(loopCondition, attributes);
      return loopCondition;
   }
   
   /**
    * Creates a {@link SEDMemoryLoopStatement} instance for the content in the given tag.
    * @param target The parent {@link ISEDDebugTarget} or {@code null} if not available.
    * @param parent The parent {@link ISEDDebugNode} or {@code null} if not available.
    * @param thread The parent {@link ISEDThread} or {@code null} if not available.
    * @param uri The Namespace URI, or the empty string if the element has no Namespace URI or if Namespace processing is not being performed.
    * @param localName  The local name (without prefix), or the empty string if Namespace processing is not being performed.
    * @param qName The qualified name (with prefix), or the empty string if qualified names are not available.
    * @param attributes The attributes attached to the element. If there are no attributes, it shall be an empty Attributes object.
    * @return The created {@link SEDMemoryLoopStatement}.
    * @throws SAXException Occurred Exception.
    */   
   protected SEDMemoryLoopStatement createLoopStatement(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryLoopStatement loopStatement = new SEDMemoryLoopStatement(target, parent, thread);
      loopStatement.setSourcePath(getSourcePath(attributes));
      fillDebugNode(loopStatement, attributes);
      fillStackFrame(loopStatement, attributes);
      return loopStatement;
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
      SEDMemoryMethodCall methodCall = new SEDMemoryMethodCall(target, parent, thread);
      methodCall.setSourcePath(getSourcePath(attributes));
      fillDebugNode(methodCall, attributes);
      fillStackFrame(methodCall, attributes);
      return methodCall;
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
      methodReturn.setSourcePath(getSourcePath(attributes));
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
      statement.setSourcePath(getSourcePath(attributes));
      fillDebugNode(statement, attributes);
      fillStackFrame(statement, attributes);
      return statement;
   }
   
   /**
    * Creates a {@link SEDMemoryMethodContract} instance for the content in the given tag.
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
   protected SEDMemoryMethodContract createMethodContract(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryMethodContract methodContract = new SEDMemoryMethodContract(target, parent, thread);
      methodContract.setSourcePath(getSourcePath(attributes));
      fillDebugNode(methodContract, attributes);
      fillStackFrame(methodContract, attributes);
      methodContract.setPreconditionComplied(isPreconditionComplied(attributes));
      methodContract.setHasNotNullCheck(hasNotNullCheck(attributes));
      methodContract.setNotNullCheckComplied(isNotNullCheckComplied(attributes));
      return methodContract;
   }
   
   /**
    * Creates a {@link SEDMemoryLoopInvariant} instance for the content in the given tag.
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
   protected SEDMemoryLoopInvariant createLoopInvariant(ISEDDebugTarget target, ISEDDebugNode parent, ISEDThread thread, String uri, String localName, String qName, Attributes attributes) throws SAXException {
      SEDMemoryLoopInvariant loopInvariant = new SEDMemoryLoopInvariant(target, parent, thread);
      loopInvariant.setSourcePath(getSourcePath(attributes));
      fillDebugNode(loopInvariant, attributes);
      fillStackFrame(loopInvariant, attributes);
      loopInvariant.setInitiallyValid(isInitiallyValid(attributes));
      return loopInvariant;
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
      SEDMemoryTermination termination = new SEDMemoryTermination(target, parent, thread, isVerified(attributes));
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
    * Returns the source path value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getSourcePath(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_SOURCE_PATH);
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
    * Returns the verified value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isVerified(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_VERIFIED));
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
   
   /**
    * Returns the type ID value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getTypeId(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_TYPE_ID);
   }
   
   /**
    * Returns the annotation content value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getAnnotationContent(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_CONTENT);
   }
   
   /**
    * Returns the enabled value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isEnabled(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_ENABLED));
   }
   
   /**
    * Returns the highlight background value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isHighlightBackground(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_HIGHLIGHT_BACKGROUND));
   }
   
   /**
    * Returns the highlight foreground value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isHighlightForeground(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SEDXMLWriter.ATTRIBUTE_HIGHLIGHT_FOREGROUND));
   }
   
   /**
    * Returns the background color value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected RGB getBackgroundColor(Attributes attributes) {
      return StringConverter.asRGB(attributes.getValue(SEDXMLWriter.ATTRIBUTE_BACKGROUND_COLOR));
   }
   
   /**
    * Returns the foreground color value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected RGB getForegroundColor(Attributes attributes) {
      return StringConverter.asRGB(attributes.getValue(SEDXMLWriter.ATTRIBUTE_FOREGROUND_COLOR));
   }
   
   /**
    * Returns the annotation link source value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getAnnotationLinkSource(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_ANNOTATION_LINK_SOURCE);
   }
   
   /**
    * Returns the annotation link target value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getAnnotationLinkTarget(Attributes attributes) {
      return attributes.getValue(SEDXMLWriter.ATTRIBUTE_ANNOTATION_LINK_TARGET);
   }
}