/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution;

import java.util.Map;
import java.util.Map.Entry;

import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;

/**
 * Provides the basic functionality for classes like {@link ExecutionNodeWriter} and
 * {@link SymbolicLayoutWriter} which encodes an object structure as XML.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractWriter {
    /**
     * New line.
     */
    public static final String NEW_LINE = StringUtil.NEW_LINE;

    /**
     * The used leading white space in each level.
     */
    public static final String LEADING_WHITE_SPACE_PER_LEVEL = "   ";

    /**
     * The default encoding.
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
     * Appends an empty tag to the given {@link StringBuilder}.
     *
     * @param level The level.
     * @param tagName The tag name.
     * @param attributeValues The attributes.
     * @param sb The {@link StringBuilder} to append to.
     */
    protected void appendEmptyTag(int level, String tagName, Map<String, String> attributeValues,
            StringBuilder sb) {
        XMLUtil.appendEmptyTag(level, tagName, attributeValues, sb);
    }

    /**
     * Appends a start tag to the given {@link StringBuilder}.
     *
     * @param level The level.
     * @param tagName The tag name.
     * @param attributeValues The attributes.
     * @param sb The {@link StringBuilder} to append to.
     */
    protected void appendStartTag(int level, String tagName, Map<String, String> attributeValues,
            StringBuilder sb) {
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
     * Appends an end tag to the given {@link StringBuilder}.
     *
     * @param level The level.
     * @param tagName The tag name.
     * @param sb The {@link StringBuilder} to append to.
     */
    protected void appendEndTag(int level, String tagName, StringBuilder sb) {
        appendWhiteSpace(level, sb);
        sb.append("</");
        sb.append(tagName);
        sb.append(">");
        appendNewLine(sb);
    }

    /**
     * Adds leading white space to the {@link StringBuilder}.
     *
     * @param level The level in the tree used for leading white space (formatting).
     * @param sb The {@link StringBuilder} to write to.
     */
    protected void appendWhiteSpace(int level, StringBuilder sb) {
        sb.append(LEADING_WHITE_SPACE_PER_LEVEL.repeat(Math.max(0, level)));
    }

    /**
     * Adds an XML attribute to the given {@link StringBuilder}.
     *
     * @param attributeName The attribute name.
     * @param value The attribute value.
     * @param sb The {@link StringBuilder} to write to.
     */
    protected void appendAttribute(String attributeName, String value, StringBuilder sb) {
        if (attributeName != null && value != null) {
            sb.append(" ");
            sb.append(attributeName);
            sb.append("=\"");
            sb.append(XMLUtil.encodeText(value));
            sb.append("\"");
        }
    }

    /**
     * Adds an XML header to the given {@link StringBuilder}.
     *
     * @param encoding The encoding to use.
     * @param sb The {@link StringBuilder} to write to.
     */
    protected void appendXmlHeader(String encoding, StringBuilder sb) {
        sb.append("<?xml version=\"1.0\"");
        appendAttribute(ATTRIBUTE_ENCODING, encoding, sb);
        sb.append("?>");
        appendNewLine(sb);
    }

    /**
     * Adds a line break to the given {@link StringBuilder}.
     *
     * @param sb The {@link StringBuilder} to write to.
     */
    protected void appendNewLine(StringBuilder sb) {
        sb.append(NEW_LINE);
    }
}
