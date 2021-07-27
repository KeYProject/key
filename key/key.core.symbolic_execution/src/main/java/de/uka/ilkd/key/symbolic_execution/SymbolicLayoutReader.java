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
import java.util.Map;
import java.util.Map.Entry;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociationValueContainer;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicElement;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;

/**
 * Allows to read XML files which contains an object model
 * written via an {@link SymbolicLayoutWriter}.
 * @author Martin Hentschel
 * @see SymbolicLayoutWriter
 */
public class SymbolicLayoutReader {
   /**
    * Reads the given {@link File}.
    * @param file The {@link File} to read.
    * @return The root of the model.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public ISymbolicLayout read(File file) throws ParserConfigurationException, SAXException, IOException {
      return read(new FileInputStream(file));
   }

   /**
    * Reads from the given {@link InputStream} and closes it.
    * @param in The {@link InputStream} to read from.
    * @return The root of the model.
    * @throws ParserConfigurationException Occurred Exception.
    * @throws SAXException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public ISymbolicLayout read(InputStream in) throws ParserConfigurationException, SAXException, IOException {
      if (in != null) {
         try {
            // Parse XML file
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setNamespaceAware(true);
            SAXParser saxParser = factory.newSAXParser();
            SEDSAXHandler handler = new SEDSAXHandler();
            saxParser.parse(in, handler);
            // Get root
            ISymbolicLayout root = handler.getRoot();
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
    * {@link DefaultHandler} implementation used in {@link ExecutionNodeReader#read(InputStream)}.
    * @author Martin Hentschel
    */
   private class SEDSAXHandler extends DefaultHandler {
      /**
       * The root of the model.
       */
      private ISymbolicLayout root;

      /**
       * The hierarchy in building phase.
       */
      private Deque<Object> parentStack = new LinkedList<Object>();

      /**
       * Maps each unique object ID to the instantiated {@link ISymbolicObject}.
       */
      private Map<String, ISymbolicObject> objectIdMapping = new LinkedHashMap<String, ISymbolicObject>();

      /**
       * Maps a {@link KeYlessAssociation} to its target object ID.
       */
      private Map<KeYlessAssociation, String> associationTargetMapping = new LinkedHashMap<KeYlessAssociation, String>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         Object parent = parentStack.peekFirst();
         if (isModel(uri, localName, qName)) {
            if (root == null) {
               root = new KeYlessLayout();
               parentStack.addFirst(root);
            }
            else {
               throw new SAXException("Model found a second time.");
            }
         }
         else if (isState(uri, localName, qName)) {
            if (!(parent instanceof KeYlessLayout)) {
               throw new SAXException("Found state in wrong hierarchy.");
            }
            KeYlessState state = new KeYlessState(getName(attributes));
            if (((KeYlessLayout)parent).getState() != null) {
               throw new SAXException("State found a second time.");
            }
            ((KeYlessLayout)parent).setState(state);
            parentStack.addFirst(state);
         }
         else if (isObject(uri, localName, qName)) {
            if (!(parent instanceof KeYlessLayout)) {
               throw new SAXException("Found object in wrong hierarchy.");
            }
            KeYlessObject object = new KeYlessObject(getName(attributes), getTypeString(attributes));
            ((KeYlessLayout)parent).addObject(object);
            parentStack.addFirst(object);
            objectIdMapping.put(getId(attributes), object);
         }
         else if (isValue(uri, localName, qName)) {
            if (!(parent instanceof AbstractKeYlessAssociationValueContainer)) {
               throw new SAXException("Found value in wrong hierarchy.");
            }
            KeYlessValue value = new KeYlessValue(getName(attributes), getProgramVariableString(attributes), isArrayIndex(attributes), getArrayIndexString(attributes), getValueString(attributes), getTypeString(attributes), getConditionString(attributes));
            ((AbstractKeYlessAssociationValueContainer)parent).addValue(value);
            parentStack.addFirst(value);
         }
         else if (isAssociation(uri, localName, qName)) {
            if (!(parent instanceof AbstractKeYlessAssociationValueContainer)) {
               throw new SAXException("Found association in wrong hierarchy.");
            }
            KeYlessAssociation association = new KeYlessAssociation(getName(attributes), getProgramVariableString(attributes), isArrayIndex(attributes), getArrayIndexString(attributes), getConditionString(attributes));
            ((AbstractKeYlessAssociationValueContainer)parent).addAssociation(association);
            parentStack.addFirst(association);
            associationTargetMapping.put(association, getTarget(attributes));
         }
         else if (isEquivalenceClass(uri, localName, qName)) {
            if (!(parent instanceof KeYlessLayout)) {
               throw new SAXException("Found equivalence class in wrong hierarchy.");
            }
            KeYlessEquivalenceClass ec = new KeYlessEquivalenceClass(getRepresentativeTerm(attributes));
            ((KeYlessLayout)parent).addEquivalenceClass(ec);
            parentStack.addFirst(ec);
         }
         else if (isTerm(uri, localName, qName)) {
            if (!(parent instanceof ISymbolicEquivalenceClass)) {
               throw new SAXException("Found term in wrong hierarchy.");
            }
            ((KeYlessEquivalenceClass)parent).addTermString(getTerm(attributes));
         }
         else {
            throw new SAXException("Unsupported tag \"" + localName + "\".");
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (!isTerm(uri, localName, qName)) {
            parentStack.removeFirst();
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endDocument() throws SAXException {
         // Fill associations with target references
         for (Entry<KeYlessAssociation, String> entry : associationTargetMapping.entrySet()) {
            ISymbolicObject target = objectIdMapping.get(entry.getValue());
            if (target == null) {
               throw new SAXException("Association target object with id \"" + entry.getValue() + "\" is not available.");
            }
            entry.getKey().setTarget(target);
         }
      }

      /**
       * Returns the root of the model.
       * @return The root of the model.
       */
      public ISymbolicLayout getRoot() {
         return root;
      }
   }

   /**
    * Checks if the currently parsed tag represents an {@link ISymbolicLayout}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link ISymbolicLayout}, {@code false} is something else.
    */
   protected boolean isModel(String uri, String localName, String qName) {
      return SymbolicLayoutWriter.TAG_MODEL.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an {@link ISymbolicAssociation}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link ISymbolicAssociation}, {@code false} is something else.
    */
   protected boolean isAssociation(String uri, String localName, String qName) {
      return SymbolicLayoutWriter.TAG_ASSOCIATION.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an {@link ISymbolicValue}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link ISymbolicValue}, {@code false} is something else.
    */
   protected boolean isValue(String uri, String localName, String qName) {
      return SymbolicLayoutWriter.TAG_VALUE.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an {@link ISymbolicObject}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link ISymbolicObject}, {@code false} is something else.
    */
   protected boolean isObject(String uri, String localName, String qName) {
      return SymbolicLayoutWriter.TAG_OBJECT.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an {@link ISymbolicState}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link ISymbolicState}, {@code false} is something else.
    */
   protected boolean isState(String uri, String localName, String qName) {
      return SymbolicLayoutWriter.TAG_STATE.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents an {@link ISymbolicEquivalenceClass}.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents an {@link ISymbolicEquivalenceClass}, {@code false} is something else.
    */
   protected boolean isEquivalenceClass(String uri, String localName, String qName) {
      return SymbolicLayoutWriter.TAG_EQUIVALENCE_CLASS.equals(qName);
   }

   /**
    * Checks if the currently parsed tag represents a term.
    * @param uri The URI.
    * @param localName THe local name.
    * @param qName The qName.
    * @return {@code true} represents a term, {@code false} is something else.
    */
   protected boolean isTerm(String uri, String localName, String qName) {
      return SymbolicLayoutWriter.TAG_TERM.equals(qName);
   }

   /**
    * Returns the value value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getValueString(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_VALUE);
   }

   /**
    * Returns the condition value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getConditionString(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_CONDITION);
   }

   /**
    * Returns the type value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getTypeString(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_TYPE);
   }

   /**
    * Returns the program variable value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getProgramVariableString(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_PROGRAM_VARIABLE);
   }

   /**
    * Returns the name value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getName(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_NAME);
   }

   /**
    * Returns the array index value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getArrayIndexString(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_ARRAY_INDEX);
   }

   /**
    * Returns the is array index flag.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected boolean isArrayIndex(Attributes attributes) {
      return Boolean.parseBoolean(attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_IS_ARRAY_INDEX));
   }

   /**
    * Returns the ID value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getId(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_XML_ID);
   }

   /**
    * Returns the target value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getTarget(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_TARGET);
   }

   /**
    * Returns the representative term value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getRepresentativeTerm(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_REPRESENTATIVE);
   }

   /**
    * Returns the term value.
    * @param attributes The {@link Attributes} which provides the content.
    * @return The value.
    */
   protected String getTerm(Attributes attributes) {
      return attributes.getValue(SymbolicLayoutWriter.ATTRIBUTE_TERM);
   }


   /**
    * An implementation of {@link ISymbolicElement} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static abstract class AbstractKeYlessElement implements ISymbolicElement {
      /**
       * {@inheritDoc}
       */
      @Override
      public IModelSettings getSettings() {
         return null;
      }
   }

   /**
    * An implementation of {@link ISymbolicLayout} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessLayout extends AbstractKeYlessElement implements ISymbolicLayout {
      /**
       * The state.
       */
      private ISymbolicState state;

      /**
       * The objects.
       */
      private ImmutableList<ISymbolicObject> objects = ImmutableSLList.nil();

      /**
       * The symbolic equivalence classes.
       */
      private ImmutableList<ISymbolicEquivalenceClass> equivalenceClasses = ImmutableSLList.nil();

      /**
       * {@inheritDoc}
       */

      @Override
      public ISymbolicState getState() {
         return state;
      }

      /**
       * Sets the state.
       * @param state The state to set.
       */
      public void setState(ISymbolicState state) {
         this.state = state;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<ISymbolicObject> getObjects() {
         return objects;
      }

      /**
       * Add a new child {@link ISymbolicObject}.
       * @param object The {@link ISymbolicObject} to add.
       */
      public void addObject(ISymbolicObject object) {
         objects = objects.append(object);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<ISymbolicEquivalenceClass> getEquivalenceClasses() {
         return equivalenceClasses;
      }

      /**
       * Add a new child {@link ISymbolicEquivalenceClass}.
       * @param object The {@link ISymbolicEquivalenceClass} to add.
       */
      public void addEquivalenceClass(ISymbolicEquivalenceClass ec) {
         equivalenceClasses = equivalenceClasses.append(ec);
      }
   }

   /**
    * An implementation of {@link ISymbolicAssociationValueContainer} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static abstract class AbstractKeYlessAssociationValueContainer extends AbstractKeYlessElement implements ISymbolicAssociationValueContainer {
      /**
       * The associations.
       */
      private ImmutableList<ISymbolicAssociation> associations = ImmutableSLList.nil();

      /**
       * The values.
       */
      private ImmutableList<ISymbolicValue> values = ImmutableSLList.nil();

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<ISymbolicAssociation> getAssociations() {
         return associations;
      }

      /**
       * Adds a new child {@link ISymbolicAssociation}
       * @param association The {@link ISymbolicAssociation} to add.
       */
      public void addAssociation(ISymbolicAssociation association) {
         associations = associations.append(association);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<ISymbolicValue> getValues() {
         return values;
      }

      /**
       * Adds a new child {@link ISymbolicValue}.
       * @param value The value to add.
       */
      public void addValue(ISymbolicValue value) {
         values = values.append(value);
      }
   }

   /**
    * An implementation of {@link ISymbolicState} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessState extends AbstractKeYlessAssociationValueContainer implements ISymbolicState {
      /**
       * The name.
       */
      private String name;

      /**
       * Constructor.
       * @param name The name.
       */
      public KeYlessState(String name) {
         super();
         this.name = name;
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
      public ISymbolicAssociation getAssociation(IProgramVariable programVariable,
                                                 boolean isArrayIndex,
                                                 Term arrayIndex,
                                                 Term condition) {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ISymbolicValue getValue(IProgramVariable programVariable,
                                     boolean isArrayIndex,
                                     Term arrayIndex,
                                     Term condition) {
         return null;
      }
   }

   /**
    * An implementation of {@link ISymbolicObject} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessObject extends AbstractKeYlessAssociationValueContainer implements ISymbolicObject {
      /**
       * The name.
       */
      private String nameString;

      /**
       * The type.
       */
      private String typeString;

      /**
       * Constructor.
       * @param nameString The name.
       * @param typeString The type.
       */
      public KeYlessObject(String nameString, String typeString) {
         super();
         this.nameString = nameString;
         this.typeString = typeString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return "Object " + getNameString();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getName() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getNameString() {
         return nameString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Sort getType() {
         return null;
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
      public ISymbolicAssociation getAssociation(IProgramVariable programVariable,
                                                 boolean isArrayIndex,
                                                 Term arrayIndex,
                                                 Term condition) {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ISymbolicValue getValue(IProgramVariable programVariable,
                                     boolean isArrayIndex,
                                     Term arrayIndex,
                                     Term condition) {
         return null;
      }
   }

   /**
    * An implementation of {@link ISymbolicValue} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessValue extends AbstractKeYlessElement implements ISymbolicValue {
      /**
       * The program variable.
       */
      private String programVariableString;

      /**
       * The value.
       */
      private String valueString;

      /**
       * The type.
       */
      private String typeString;

      /**
       * The name.
       */
      private String name;

      /**
       * The is array index flag.
       */
      private boolean isArrayIndex;

      /**
       * The array index.
       */
      private String arrayIndexString;

      /**
       * The optional condition under which this value is valid.
       */
      private String conditionString;

      /**
       * Constructor.
       * @param name The name.
       * @param programVariableString The program variable.
       * @param isArrayIndex The is array index flag.
       * @param arrayIndexString The array index.
       * @param valueString The value.
       * @param typeString The type.
       * @param conditionString The optional condition under which this value is valid.
       */
      public KeYlessValue(String name, String programVariableString, boolean isArrayIndex, String arrayIndexString, String valueString, String typeString, String conditionString) {
         super();
         this.name = name;
         this.programVariableString = programVariableString;
         this.isArrayIndex = isArrayIndex;
         this.arrayIndexString = arrayIndexString;
         this.valueString = valueString;
         this.typeString = typeString;
         this.conditionString = conditionString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return "Value of " + getName() + " is " + getValueString();
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
      public String getProgramVariableString() {
         return programVariableString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getValue() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getValueString() {
         return valueString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Sort getType() {
         return null;
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
      public String getName() {
         return name;
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
      public Term getArrayIndex() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getArrayIndexString() {
         return arrayIndexString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getCondition() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getConditionString() {
         return conditionString;
      }
   }

   /**
    * An implementation of {@link ISymbolicAssociation} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessAssociation extends AbstractKeYlessElement implements ISymbolicAssociation {
      /**
       * The program variable.
       */
      private String programVariableString;

      /**
       * The target.
       */
      private ISymbolicObject target;

      /**
       * The name.
       */
      private String name;

      /**
       * The is array index flag.
       */
      private boolean isArrayIndex;

      /**
       * The array index.
       */
      private String arrayIndexString;

      /**
       * The optional condition under which this association is valid.
       */
      private String conditionString;

      /**
       * Constructor.
       * @param name The name.
       * @param programVariableString The program variable.
       * @param isArrayIndex The is array index flag.
       * @param arrayIndexString The array index.
       * @param conditionString The optional condition under which this association is valid.
       */
      public KeYlessAssociation(String name, String programVariableString, boolean isArrayIndex, String arrayIndexString, String conditionString) {
         this(name, programVariableString, isArrayIndex, arrayIndexString, null, conditionString);
      }

      /**
       * Constructor.
       * @param name The name.
       * @param programVariableString The program variable.
       * @param isArrayIndex The is array index flag.
       * @param arrayIndexString The array index.
       * @param target The target.
       * @param conditionString The optional condition under which this association is valid.
       */
      public KeYlessAssociation(String name, String programVariableString, boolean isArrayIndex, String arrayIndexString, ISymbolicObject target, String conditionString) {
         super();
         this.name = name;
         this.programVariableString = programVariableString;
         this.isArrayIndex = isArrayIndex;
         this.arrayIndexString = arrayIndexString;
         this.target = target;
         this.conditionString = conditionString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return "Association " + getName() + " to " + getTarget();
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
      public String getProgramVariableString() {
         return programVariableString;
      }

      /**
       * Sets the target.
       * @param target The target to set.
       */
      public void setTarget(ISymbolicObject target) {
         this.target = target;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ISymbolicObject getTarget() {
         return target;
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
      public boolean isArrayIndex() {
         return isArrayIndex;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getArrayIndex() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getArrayIndexString() {
         return arrayIndexString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getCondition() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getConditionString() {
         return conditionString;
      }
   }

   /**
    * An implementation of {@link ISymbolicEquivalenceClass} which is independent
    * from KeY and provides such only children and default attributes.
    * @author Martin Hentschel
    */
   public static class KeYlessEquivalenceClass extends AbstractKeYlessElement implements ISymbolicEquivalenceClass {
      /**
       * The terms.
       */
      private ImmutableList<String> termStrings;

      /**
       * The representative term.
       */
      private String representativeString;

      /**
       * Constructor.
       * @param representativeString The representative term.
       */
      public KeYlessEquivalenceClass(String representativeString) {
         this(ImmutableSLList.<String>nil(), representativeString);
      }

      /**
       * Constructor.
       * @param termStrings The terms.
       * @param representativeString The representative term.
       */
      public KeYlessEquivalenceClass(ImmutableList<String> termStrings, String representativeString) {
         this.termStrings = termStrings;
         this.representativeString = representativeString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<Term> getTerms() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public ImmutableList<String> getTermStrings() {
         return termStrings;
      }

      /**
       * Add a new child term string.
       * @param object The term string to add.
       */
      public void addTermString(String termString) {
         this.termStrings = termStrings.append(termString);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Term getRepresentative() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getRepresentativeString() {
         return representativeString;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean containsTerm(Term term) {
         return false;
      }
   }
}