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

import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * Provides the basic functionality for classes like {@link ExecutionNodeWriter}
 * and {@link SymbolicConfigurationWriter} which encodes an object structure as XML.
 * @author Martin Hentschel
 */
public abstract class AbstractWriter {
   /**
    * New line.
    */
   public static final String NEW_LINE = System.getProperty("line.separator");
   
   /**
    * The used leading white space in each level.
    */
   public static final String LEADING_WHITE_SPACE_PER_LEVEL = "   ";
   
   /**
    * The default enconding.
    */
   public static final String DEFAULT_ENCODING = "UTF-8";

   /**
    * Attribute name to store encodings.
    */
   public static final String ATTRIBUTE_ENCODING = "encoding";

   /**
    * Attribute name to store the XML ID.
    */
   public static final String ATTRIBUTE_XML_ID = "xml:id";

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