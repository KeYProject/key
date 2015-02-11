package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;

public interface IJMLValidationContext {

   IASTNode getJMLNode();

   ICompilationUnit getCompilationUnit();

   List<CommentRange> getJMLComments();
}
