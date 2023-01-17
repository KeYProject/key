// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

import java.io.*;
import java.util.Enumeration;
import java.util.Properties;
import java.util.Vector;

/**
 * Information about the tags in a java style structured comment (DocComment). Such a comment has an
 * introductionary description and a list of tagged descriptions.
 *
 * @author RN
 * @author AL
 */

public class TagInfo {

    /**
     * the empty enumeration
     */

    private final static Enumeration EMPTY_ENUMERATION = new Vector(0).elements();
    /**
     * the raw (unparsed) comment string.
     */

    String rawComment;
    /**
     * the introductionary comment lines without comment characters.
     */

    String introText;
    /**
     * the tags contained in the comment. This is required to obtain the order in which the tags
     * occur
     */

    Vector<String> tagNames;
    /**
     * the tags and their string values. Tags are stored without the leading <tt>@</tt> sign
     */

    Properties tagValues;
    boolean analyzed;

    /**
     * Creates a new instance from the given string. The given string must not be <CODE>null</CODE>.
     *
     * @param comment the string containing the comment.
     */

    protected TagInfo(DocComment dc) {
        rawComment = dc.getText();
    }

    /**
     * Strips comment characters from the beginning and end of the given string representing a
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
            if (result.charAt(left) == '/')
                left++;
            while ((left <= right) && (result.charAt(left) == '*'))
                left++;
            if (result.charAt(right) == '/')
                right--;
            while ((left <= right) && (result.charAt(right) == '*'))
                right--;
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
                        tagNames = new Vector<String>();
                        tagValues = new Properties();
                        // finish a prior comment region (if existent)
                    }
                    if (pw != null) {
                        if (currentTag == null) {
                            introText = sw.toString();
                        } else {
                            tagValues.put(currentTag, sw.toString());
                            // start the new tag
                        }
                    }
                    sw = new StringWriter();
                    pw = new PrintWriter(sw);
                    int pos = 1;
                    while ((pos < line.length()) && !(Character.isWhitespace(line.charAt(pos))))
                        pos++;
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
                // finish a prior comment region (if existent)
            }
            if (pw != null) {
                if (currentTag == null) {
                    introText = sw.toString();
                } else {
                    tagValues.put(currentTag, sw.toString());
                }
            }
        } catch (IOException ioe) {
            // don't know how to handle this!
            ioe.printStackTrace();
        }
        analyzed = true;
    }

    /**
     * Returns the introductionary text of the comment. This is the text starting at the beginning
     * of the comment to the first tag.
     *
     * @return the intro of the comment.
     */

    public String getIntro() {
        if (!analyzed)
            parseRawComment();
        return (introText == null) ? "" : introText;
    }

    /**
     * Determines whether or not there are tags contained in the underlying comment.
     *
     * @return <tt>true</tt> iff the comment contains tags.
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
        if (!analyzed)
            parseRawComment();
        return (tagNames == null) ? 0 : tagNames.size();
    }

    /**
     * return an enumeration of tags contained in the comment in order of their apperance in the
     * comment.
     *
     * @return an non-empty enumeration object.
     */

    public Enumeration getTags() {
        if (!analyzed)
            parseRawComment();
        if (tagNames == null) {
            return EMPTY_ENUMERATION;
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
            if (!analyzed)
                parseRawComment();
            if (tagValues != null) {
                result = tagValues.getProperty(tag, null);
            }
        }
        return result;
    }
}
