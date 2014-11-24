package org.key_project.jmlediting.core.parser;

import org.key_project.jmlediting.core.dom.IBehaviorSpecification;
import org.key_project.jmlediting.core.dom.IMethodSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationCase;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;

public interface IJMLParser {
   
   IMethodSpecification parseMethodSpecification(String text, int start, int end) throws ParserException;
   ISpecificationCase parseSpecificationCase(String text, int start, int end) throws ParserException;
   IBehaviorSpecification parseBehaviorSpecification(String text, int start, int end) throws ParserException;
   ISpecificationStatement parseSpecificationStatement(String text, int start, int end) throws ParserException;

}
