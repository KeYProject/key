package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;

/**
 * Specifies an Parser for JML.
 *
 * @author Moritz Lichter
 *
 */
public interface IJMLParser extends ParseFunction {

   /**
    * Parses a JML annotation in the given text from start index (including) to
    * end index (excluding).
    *
    * @param text
    *           the text to parse an annotation from
    * @param start
    *           the inclusive start index of the annotation
    * @param end
    *           the exclusive end index of the annotation
    * @return the root {@link IASTNode} of the parse result
    * @throws ParserException
    *            if Parsing encountered an error
    */
   @Override
   IASTNode parse(String text, int start, int end) throws ParserException;

   /**
    * Shorthand function to parse a CommentRange instead of passing the offsets.
    * 
    * @param text
    *           the text to parse
    * @param range
    *           the comment to parse in the text
    * @return the root {@link IASTNode} of the parse result
    * @throws ParserException
    *            if Parsing encountered an error
    */
   IASTNode parse(String text, CommentRange range) throws ParserException;

}
