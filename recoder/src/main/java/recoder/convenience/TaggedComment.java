/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import java.io.*;
import java.util.Enumeration;
import java.util.Properties;
import java.util.Vector;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * this class represents a java style structured comment. Such a comment has an introductionary
 * description and a list of tagged descriptions.
 *
 * @author Rainer Neumann
 * @deprecated This class will be integrated into DocComment.
 */
@Deprecated
public class TaggedComment {
    private static final Logger LOGGER = LoggerFactory.getLogger(TaggedComment.class);

    /**
     * a simple empty vector used for returning empty enumerations
     */
    private static final Vector emptyVector = new Vector();
    /**
     * the empty enumeration
     */
    private static final Enumeration emptyEnumeration = emptyVector.elements();
    /**
     * the raw (unparsed) comment string.
     */
    protected final String rawComment;
    /**
     * indicates that the comment has been analyzed
     */
    protected boolean analyzed;
    /**
     * the introductionary comment lines without comment characters.
     */
    protected String introText;
    /**
     * the tags contained in the comment. This is required to obtain the order in which the tags
     * occur
     */
    protected Vector tagNames;
    /**
     * the tags and their string values. Tags are stored without the leading <tt>@</tt> sign
     */
    protected Properties tagValues;

    /**
     * creates a new instance from the given string. The given string <b>must not </b> be
     * <tt>null</tt>!
     *
     * @param comment the string containing the comment
     */
    public TaggedComment(String comment) {
        rawComment = comment;
    }

    /**
     * simple test method for this class
     */
    public static void main(String[] args) {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        pw.println("/** line1 */");
        pw.println("/*  line2 *");
        pw.println("  * @tag1 */");
        pw.print("    @tag2 value */");
        TaggedComment tc = new TaggedComment(sw.toString());
        System.out.println("intro:");
        System.out.println(tc.getIntro());
        for (Enumeration tags = tc.getTags(); tags.hasMoreElements();) {
            String tag = (String) tags.nextElement();
            System.out.println("@" + tag);
            System.out.println(tc.getTagValue(tag));
        }
    }

    /**
     * strips comment characters from the beginning and end of the given string representing a
     * single line.
     *
     * @param line the string representing the line. The line is assumed to be non empty.
     * @return the stripped and trimmed string
     */
    protected String stripCommentChars(String line) {
        String result = line.trim();
        if (result.length() > 0) {
            int left = 0;
            int right = result.length() - 1;
            if (result.charAt(left) == '/') {
                left++;
            }
            while ((left <= right) && (result.charAt(left) == '*')) {
                left++;
            }
            if (result.charAt(right) == '/') {
                right--;
            }
            while ((left <= right) && (result.charAt(right) == '*')) {
                right--;
            }
            if (left <= right) {
                result = result.substring(left, right + 1).trim();
            } else {
                result = "";
            }
        }
        return result;
    }

    /**
     * parses the raw comment string and computes the intro and tag values.
     */
    protected void parseRawComment() {
        LineNumberReader lnr = new LineNumberReader(new StringReader(rawComment));
        boolean done = false;
        String currentTag = null;
        PrintWriter pw = null;
        StringWriter sw = null;
        String line;
        try {
            while ((line = lnr.readLine()) != null) {
                line = stripCommentChars(line);
                if (line.startsWith("@")) { // tag recognized
                    // initialize data structures
                    if (tagNames == null) {
                        tagNames = new Vector();
                        tagValues = new Properties();
                    }
                    // finish a prior comment region (if existent)
                    if (pw != null) {
                        if (currentTag == null) {
                            introText = sw.toString();
                        } else {
                            tagValues.put(currentTag, sw.toString());
                        }
                    }
                    // start the new tag
                    sw = new StringWriter();
                    pw = new PrintWriter(sw);
                    int pos = 1;
                    while ((pos < line.length()) && !(Character.isWhitespace(line.charAt(pos)))) {
                        pos++;
                    }
                    currentTag = line.substring(1, pos);
                    tagNames.addElement(currentTag);
                    line = line.substring(pos).trim();
                } else { // this continues previous messages
                    if (pw == null) {
                        sw = new StringWriter();
                        pw = new PrintWriter(sw);
                    } else {
                        pw.println("");
                    }
                }
                pw.print(line);
            }
            // finish a prior comment region (if existent)
            if (pw != null) {
                if (currentTag == null) {
                    introText = sw.toString();
                } else {
                    tagValues.put(currentTag, sw.toString());
                }
            }
        } catch (IOException ioe) {
            // don't know how to handle this!
            LOGGER.warn("Failed to parse comment", ioe);
        }
        analyzed = true;
    }

    /**
     * returns the introductionary text of the comment. This is the text starting at the beginning
     * of the comment to the first tag.
     *
     * @return the intro of the comment
     */
    public String getIntro() {
        if (!analyzed) {
            parseRawComment();
        }
        return (introText == null) ? "" : introText;
    }

    /**
     * determines whether or not there are tags contained in the underlying comment.
     *
     * @return <tt>true</tt> iff the comment contains tags
     */
    public boolean hasTags() {
        return getTagCount() > 0;
    }

    /**
     * determines the number of tags in the underlying comment
     *
     * @return the number of tags specified in the comment
     */
    public int getTagCount() {
        if (!analyzed) {
            parseRawComment();
        }
        return (tagNames == null) ? 0 : tagNames.size();
    }

    /**
     * return an enumeration of tags contained in the comment in order of their apperance in the
     * comment.
     *
     * @return an non-empty enumeration object.
     */
    public Enumeration getTags() {
        if (!analyzed) {
            parseRawComment();
        }
        if (tagNames == null) {
            return emptyEnumeration;
        } else {
            return tagNames.elements();
        }
    }

    /**
     * returns the text for the given tag or <tt>null</tt> if that tag is not defined.
     *
     * @param tag the name of the tag
     * @return the value of that tag or <tt>null</tt>
     */
    public String getTagValue(String tag) {
        String result = null;
        if (tag != null) {
            if (!analyzed) {
                parseRawComment();
            }
            if (tagValues != null) {
                result = tagValues.getProperty(tag, null);
            }
        }
        return result;
    }

}
