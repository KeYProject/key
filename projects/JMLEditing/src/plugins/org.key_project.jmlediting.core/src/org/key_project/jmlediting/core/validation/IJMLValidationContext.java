package org.key_project.jmlediting.core.validation;

import java.util.List;

import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.utilities.CommentRange;

/**
 * Interface that Represents a Validation Context for JML.
 *
 * @author David Giessing
 *
 */
public interface IJMLValidationContext {

   /**
    * Returns the Source on which to operate the validation.
    *
    * @return the Source
    */
   String getSrc();

   /**
    * Returns a List of CommentRanges representing the JMLComments in the File
    * under validation.
    *
    * @return the CommentRange List
    */
   List<CommentRange> getJMLComments();

   /**
    * Returns the Java AST for the file that shall be validated.
    *
    * @return the JavaAST
    */
   CompilationUnit getJavaAST();

   /**
    * Returns the JML Parser for this context.
    * 
    * @return the JML Parser
    */
   IJMLParser getJMLParser();

}
