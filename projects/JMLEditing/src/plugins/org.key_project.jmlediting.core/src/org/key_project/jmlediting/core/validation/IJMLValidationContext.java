package org.key_project.jmlediting.core.validation;

import java.util.List;

import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.utilities.CommentRange;

public interface IJMLValidationContext {

   String getSrc();

   List<CommentRange> getJMLComments();

   CompilationUnit getJavaAST();

}
