package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * Specifies an Parser for JML.
 *
 * @author Moritz Lichter
 *
 */
public interface IJMLParser {

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
   IASTNode parse(String text, int start, int end) throws ParserException;

}
