/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

import java.util.Map;
import java.util.Map.Entry;

/**
 * Provides static methods to work with XML.
 *
 * @author Martin Hentschel
 */
public final class XMLUtil {
    /**
     * Attribute name to store encodings.
     */
    public static final String ATTRIBUTE_ENCODING = "encoding";

    /**
     * The used leading white space in each level.
     */
    public static final String LEADING_WHITE_SPACE_PER_LEVEL = "   ";

    /**
     * Forbid instances.
     */
    private XMLUtil() {
    }

    /**
     * Replaces all tags in the given text with help of the given {@link ITagReplacer}.
     *
     * @param text The text to execute replacements on.
     * @param replacer The {@link ITagReplacer} to use.
     * @return The new created text.
     */
    public static String replaceTags(String text, ITagReplacer replacer) {
        if (text != null && replacer != null) {
            StringBuilder sb = new StringBuilder();
            char[] signs = text.toCharArray();
            boolean inTag = false;
            boolean inAttribute = false;
            StringBuilder tagSB = null;
            for (char sign : signs) {
                if (!inTag) {
                    if (sign == '<') {
                        inTag = true;
                        tagSB = new StringBuilder();
                        tagSB.append(sign);
                    } else {
                        sb.append(sign);
                    }
                } else {
                    tagSB.append(sign);
                    if (sign == '>' && !inAttribute) {
                        inTag = false;
                        String replacement = replacer.replaceTag(tagSB.toString());
                        if (replacement != null) {
                            sb.append(replacement);
                        }
                    } else if (sign == '\'' || sign == '"') {
                        inAttribute = !inAttribute;
                    }
                }
            }
            return sb.toString();
        } else {
            return null;
        }
    }

    /**
     * Instances of this interface are used in {@link XMLUtil#replaceTags(String, ITagReplacer)} to
     * replace an individual found tag.
     *
     * @author Martin Hentschel
     */
    public interface ITagReplacer {
        /**
         * Replaces the given tag by something else.
         *
         * @param tag The found tag.
         * @return The replacement to use or {@code null} to remove the tag.
         */
        String replaceTag(String tag);
    }

    /**
     * This {@link ITagReplacer} can be used to render HTML into a plain text. Basically all tags
     * will be removed. Only a limited set of tags is replaced by a new plain text which improves
     * readability.
     *
     * @author Martin Hentschel
     */
    public static class HTMLRendererReplacer implements ITagReplacer {
        @Override
        public String replaceTag(String tag) {
            if (tag.startsWith("<br")) {
                return StringUtil.NEW_LINE;
            } else if (tag.startsWith("<li")) {
                return StringUtil.NEW_LINE + "- ";
            } else if (tag.startsWith("</ol")) {
                return StringUtil.NEW_LINE;
            } else if (tag.startsWith("</ul")) {
                return StringUtil.NEW_LINE;
            } else if (tag.startsWith("<center")) {
                return StringUtil.NEW_LINE;
            } else if (tag.startsWith("</center")) {
                return StringUtil.NEW_LINE;
            } else {
                return null;
            }
        }
    }

    /**
     * Removes all tags from the given text.
     *
     * @param text The text to remove tags from.
     * @return The text without tags.
     */
    public static String removeTags(String text) {
        if (text != null) {
            StringBuilder sb = new StringBuilder();
            char[] signs = text.toCharArray();
            boolean inTag = false;
            boolean inAttribute = false;
            for (char sign : signs) {
                if (!inTag) {
                    if (sign == '<') {
                        inTag = true;
                    } else {
                        sb.append(sign);
                    }
                } else {
                    if (sign == '>' && !inAttribute) {
                        inTag = false;
                    } else if (sign == '\'' || sign == '"') {
                        inAttribute = !inAttribute;
                    }
                }
            }
            return sb.toString();
        } else {
            return null;
        }
    }

    /**
     * <p>
     * Encodes the given text in a way that it contains no XML elements and can be used for instance
     * as plain text or attribute value.
     * </p>
     * <p>
     * The following signs are replaced:
     *
     * <pre>
     * " => &quot;quot;
     * & => &quot;amp;
     * ' => &quot;apos;
     * < => &quot;lt;
     * > => &quot;gt;
     * </pre>
     * </p>
     *
     * @param text The text to encode.
     * @return The encoded text.
     */
    public static String encodeText(String text) {
        if (text != null) {
            char[] signs = text.toCharArray();
            StringBuilder sb = new StringBuilder();
            for (char sign : signs) {
                switch (sign) {
                case '"':
                    sb.append("&quot;");
                    break;
                case '&':
                    sb.append("&amp;");
                    break;
                case '\'':
                    sb.append("&apos;");
                    break;
                case '<':
                    sb.append("&lt;");
                    break;
                case '>':
                    sb.append("&gt;");
                    break;
                default:
                    sb.append(sign);
                    break;
                }
            }
            return sb.toString();
        } else {
            return null;
        }
    }

    /**
     * Checks if the given character is valid to be used in entity names (between {@code &...;}).
     *
     * @param character The character to check.
     * @return {@code true} is valid, {@code false} is not valid.
     */
    public static boolean isEntityNameCharacter(char character) {
        return '#' == character || StringUtil.LATIN_ALPHABET_BIG.contains(String.valueOf(character))
                || StringUtil.LATIN_ALPHABET_SMALL.contains(String.valueOf(character))
                || StringUtil.NUMERALS.contains(String.valueOf(character));
    }

    /**
     * Appends an empty tag to the given {@link StringBuilder}.
     *
     * @param level The level.
     * @param tagName The tag name.
     * @param attributeValues The attributes.
     * @param sb The {@link StringBuilder} to append to.
     */
    public static void appendEmptyTag(int level, String tagName,
            Map<String, String> attributeValues, StringBuilder sb) {
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
     * Appends a start tag to the given {@link StringBuilder}.
     *
     * @param level The level.
     * @param tagName The tag name.
     * @param attributeValues The attributes.
     * @param sb The {@link StringBuilder} to append to.
     */
    public static void appendStartTag(int level, String tagName,
            Map<String, String> attributeValues, StringBuilder sb) {
        appendWhiteSpace(level, sb);
        sb.append("<");
        sb.append(tagName);
        if (attributeValues != null) {
            for (Entry<String, String> entry : attributeValues.entrySet()) {
                appendAttribute(entry.getKey(), entry.getValue(), sb);
            }
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
    public static void appendEndTag(int level, String tagName, StringBuilder sb) {
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
    public static void appendWhiteSpace(int level, StringBuilder sb) {
        sb.append(LEADING_WHITE_SPACE_PER_LEVEL.repeat(Math.max(0, level)));
    }

    /**
     * Adds an XML attribute to the given {@link StringBuilder}.
     *
     * @param attributeName The attribute name.
     * @param value The attribute value.
     * @param sb The {@link StringBuilder} to write to.
     */
    public static void appendAttribute(String attributeName, String value, StringBuilder sb) {
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
    public static void appendXmlHeader(String encoding, StringBuilder sb) {
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
    public static void appendNewLine(StringBuilder sb) {
        sb.append(StringUtil.NEW_LINE);
    }
}
