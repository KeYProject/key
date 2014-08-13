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
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.Charset;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Allows to persistent selected properties of {@link ISymbolicLayout}s
 * as XML file. Such files can be read via a {@link SymbolicLayoutReader} instance.
 * @author Martin Hentschel
 * @see SymbolicLayoutReader
 */
public class SymbolicLayoutWriter extends AbstractWriter {
   /**
    * Tag name to store {@link ISymbolicLayout}s.
    */
   public static final String TAG_MODEL = "model";
   
   /**
    * Tag name to store {@link ISymbolicState}s.
    */
   public static final String TAG_STATE = "state";

   /**
    * Tag name to store {@link ISymbolicObject}s.
    */
   public static final String TAG_OBJECT = "object";

   /**
    * Tag name to store {@link ISymbolicValue}s.
    */
   public static final String TAG_VALUE = "value";

   /**
    * Tag name to store {@link ISymbolicAssociation}s.
    */
   public static final String TAG_ASSOCIATION = "association";

   /**
    * Tag name to store {@link ISymbolicEquivalenceClass}s.
    */
   public static final String TAG_EQUIVALENCE_CLASS = "equivalenceClass";

   /**
    * Tag name to store entries of {@link ISymbolicEquivalenceClass#getTerms()}s.
    */
   public static final String TAG_TERM = "term";

   /**
    * Attribute name to store {@link ISymbolicObject#getNameString()}.
    */
   public static final String ATTRIBUTE_NAME = "name";

   /**
    * Attribute name to store {@link ISymbolicValue#getProgramVariableString()}
    * and {@link ISymbolicAssociation#getProgramVariableString()}.
    */
   public static final String ATTRIBUTE_PROGRAM_VARIABLE = "programVariable";

   /**
    * Attribute name to store {@link ISymbolicValue#getValueString()}.
    */
   public static final String ATTRIBUTE_VALUE = "value";

   /**
    * Attribute name to store {@link ISymbolicValue#getConditionString()} and
    * {@link ISymbolicAssociation#getConditionString()}.
    */
   public static final String ATTRIBUTE_CONDITION = "condition";

   /**
    * Attribute name to store {@link ISymbolicAssociation#getTarget()}.
    */
   public static final String ATTRIBUTE_TARGET = "target";

   /**
    * Attribute name to store an entry of {@link ISymbolicEquivalenceClass#getTermStrings()}
    */
   public static final String ATTRIBUTE_TERM = "term";

   /**
    * Attribute name to store {@link ISymbolicEquivalenceClass#getRepresentativeString()}.
    */
   public static final String ATTRIBUTE_REPRESENTATIVE = "representativeTerm";

   /**
    * Attribute name to store {@link ISymbolicValue#getTypeString()} and
    * {@link ISymbolicObject#getTypeString()}.
    */
   public static final String ATTRIBUTE_TYPE = "type";

   /**
    * Attribute name to store {@link ISymbolicValue#isArrayIndex()} and
    * {@link ISymbolicObject#isArrayIndex()}.
    */
   public static final String ATTRIBUTE_IS_ARRAY_INDEX = "isArrayIndex";

   /**
    * Attribute name to store {@link ISymbolicValue#getArrayIndex()} and
    * {@link ISymbolicObject#getArrayIndex()}.
    */
   public static final String ATTRIBUTE_ARRAY_INDEX = "arrayIndex";

   /**
    * Writes the given {@link ISymbolicLayout} as XML file.
    * @param model The {@link ISymbolicLayout} to save.
    * @param encoding The encoding to use.
    * @param file The {@link File} to save to.
    * @throws IOException Occurred Exception.
    */
   public void write(ISymbolicLayout model, 
                     String encoding, 
                     File file) throws IOException {
      write(model, encoding, new FileOutputStream(file));
   }
   
   /**
    * Writes the given {@link ISymbolicLayout} into the {@link OutputStream}.
    * @param node The {@link ISymbolicLayout} to save.
    * @param encoding The encoding to use.
    * @param out The {@link OutputStream} to save to. The {@link OutputStream} will be closed by this method.
    * @throws IOException Occurred Exception.
    */
   public void write(ISymbolicLayout model, 
                     String encoding, 
                     OutputStream out) throws IOException {
      if (out != null) {
         try {
            Charset charset = encoding != null ? Charset.forName(encoding) : Charset.defaultCharset();
            String xml = toXML(model, charset.displayName());
            out.write(xml.getBytes(charset));
         }
         finally {
            out.close();
         }
      }
   }
   
   /**
    * Converts the given {@link ISymbolicLayout} into XML.
    * @param node The {@link ISymbolicLayout} to convert.
    * @param encoding The encoding to use.
    * @return The created XML content.
    */
   public String toXML(ISymbolicLayout model, 
                       String encoding){
      StringBuffer sb = new StringBuffer();
      appendXmlHeader(encoding, sb);
      appendModel(0, model, sb);
      return sb.toString();
   }

   /**
    * Appends the given {@link ISymbolicLayout} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param model The {@link ISymbolicLayout} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendModel(int level, ISymbolicLayout model, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      appendStartTag(level, TAG_MODEL, attributeValues, sb);
      for (ISymbolicEquivalenceClass ec : model.getEquivalenceClasses()) {
         appendEquivalenceClass(level + 1, ec, sb);
      }
      appendState(level + 1, model, model.getState(), sb);
      for (ISymbolicObject object : model.getObjects()) {
         appendObject(level + 1, model, object, sb);
      }
      appendEndTag(level, TAG_MODEL, sb);
   }

   /**
    * Appends the given {@link ISymbolicEquivalenceClass} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param ec The {@link ISymbolicEquivalenceClass} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendEquivalenceClass(int level, ISymbolicEquivalenceClass ec, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_REPRESENTATIVE, ec.getRepresentativeString());
      appendStartTag(level, TAG_EQUIVALENCE_CLASS, attributeValues, sb);
      for (String term : ec.getTermStrings()) {
         Map<String, String> termAttributeValues = new LinkedHashMap<String, String>();
         termAttributeValues.put(ATTRIBUTE_TERM, term);
         appendEmptyTag(level + 1, TAG_TERM, termAttributeValues, sb);
      }
      appendEndTag(level, TAG_EQUIVALENCE_CLASS, sb);
   }

   /**
    * Appends the given {@link ISymbolicState} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param model The {@link ISymbolicLayout} which provides all objects.
    * @param state The {@link ISymbolicState} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendState(int level, ISymbolicLayout model, ISymbolicState state, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, state.getName());
      appendStartTag(level, TAG_STATE, attributeValues, sb);
      for (ISymbolicValue value : state.getValues()) {
         appendValue(level + 1, value, sb);
      }
      for (ISymbolicAssociation association : state.getAssociations()) {
         appendAssociation(level + 1, model, association, sb);
      }
      appendEndTag(level, TAG_STATE, sb);
   }

   /**
    * Appends the given {@link ISymbolicObject} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param model The {@link ISymbolicLayout} which provides all objects.
    * @param object The {@link ISymbolicObject} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendObject(int level, ISymbolicLayout model, ISymbolicObject object, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_XML_ID, computeObjectId(model, object));
      attributeValues.put(ATTRIBUTE_NAME, object.getNameString());
      attributeValues.put(ATTRIBUTE_TYPE, object.getTypeString());
      appendStartTag(level, TAG_OBJECT, attributeValues, sb);
      for (ISymbolicValue value : object.getValues()) {
         appendValue(level + 1, value, sb);
      }
      for (ISymbolicAssociation association : object.getAssociations()) {
         appendAssociation(level + 1, model, association, sb);
      }
      appendEndTag(level, TAG_OBJECT, sb);
   }

   /**
    * Appends the given {@link ISymbolicValue} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param value The {@link ISymbolicValue} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendValue(int level, ISymbolicValue value, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, value.getName());
      attributeValues.put(ATTRIBUTE_PROGRAM_VARIABLE, value.getProgramVariableString());
      attributeValues.put(ATTRIBUTE_IS_ARRAY_INDEX, value.isArrayIndex() + "");
      attributeValues.put(ATTRIBUTE_ARRAY_INDEX, value.getArrayIndex() + "");
      attributeValues.put(ATTRIBUTE_VALUE, value.getValueString());
      attributeValues.put(ATTRIBUTE_TYPE, value.getTypeString());
      if (value.getConditionString() != null) {
         attributeValues.put(ATTRIBUTE_CONDITION, value.getConditionString());
      }
      appendEmptyTag(level, TAG_VALUE, attributeValues, sb);
   }

   /**
    * Appends the given {@link ISymbolicAssociation} with its children to the given {@link StringBuffer}.
    * @param level The level to use.
    * @param model The {@link ISymbolicLayout} which provides all objects.
    * @param association The {@link ISymbolicAssociation} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendAssociation(int level, ISymbolicLayout model, ISymbolicAssociation association, StringBuffer sb) {
      Map<String, String> attributeValues = new LinkedHashMap<String, String>();
      attributeValues.put(ATTRIBUTE_NAME, association.getName());
      attributeValues.put(ATTRIBUTE_PROGRAM_VARIABLE, association.getProgramVariableString());
      attributeValues.put(ATTRIBUTE_IS_ARRAY_INDEX, association.isArrayIndex() + "");
      attributeValues.put(ATTRIBUTE_ARRAY_INDEX, association.getArrayIndex() + "");
      attributeValues.put(ATTRIBUTE_TARGET, computeObjectId(model, association.getTarget()));
      if (association.getConditionString() != null) {
         attributeValues.put(ATTRIBUTE_CONDITION, association.getConditionString());
      }
      appendEmptyTag(level, TAG_ASSOCIATION, attributeValues, sb);
   }

   /**
    * Computes a unique ID for the given object in the given model.
    * @param model The {@link ISymbolicLayout} which provides all objects.
    * @param object The {@link ISymbolicObject} to compute its unique ID.
    * @return The unique ID.
    */
   protected String computeObjectId(ISymbolicLayout model, ISymbolicObject object) {
      int i = 0;
      int index = -1;
      Iterator<ISymbolicObject> iter = model.getObjects().iterator();
      while (index < 0 && iter.hasNext()) {
         ISymbolicObject next = iter.next();
         if (next == object) {
            index = i;
         }
         i++;
      }
      return "o" + (index + 1);
   }
}