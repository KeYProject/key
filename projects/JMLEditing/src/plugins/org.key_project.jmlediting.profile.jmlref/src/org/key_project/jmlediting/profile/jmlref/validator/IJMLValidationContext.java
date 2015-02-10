package org.key_project.jmlediting.profile.jmlref.validator;

import org.eclipse.jdt.core.ICompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;

public interface IJMLValidationContext {

   IASTNode getJMLNode();

   ICompilationUnit getCompilationUnit();
}
