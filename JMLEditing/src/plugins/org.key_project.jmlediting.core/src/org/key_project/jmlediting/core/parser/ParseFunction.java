package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * A {@link ParseFunction} is a function which encapsulates a special sort for
 * the grammar. The {@link ParseFunction} is used to be able to combine
 * {@link ParseFunction}. If we would use Java 8, it would be treated as an
 * functional interface.
 *
 * @author Moritz Lichter
 *
 */
public interface ParseFunction {
   /**
    * Parses the text for a keyword. The method is invoked with the start index
    * after the detected keyword. The parser is allowed to parse until end
    * position (exclusively). Text is guaranteed to have at least length end, so
    * end-1 is the maximum guaranteed valid character request. If the parser is
    * not able to parse, it must throw an ParserException.
    *
    * @param text
    *           the string to parse
    * @param start
    *           the start index to start parsing at
    * @param end
    *           the maximum position to parse to
    * @return the ast node parsed from the string. Null is allowed it the parser
    *         did not parse anything.
    * @throws ParserException
    *            when parsing encounters an error
    */
   IASTNode parse(String text, int start, int end) throws ParserException;
}