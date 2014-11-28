package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IASTNode;

public interface IJMLParser {
   
   IASTNode parse(String text, int start, int end) throws ParserException;

}
