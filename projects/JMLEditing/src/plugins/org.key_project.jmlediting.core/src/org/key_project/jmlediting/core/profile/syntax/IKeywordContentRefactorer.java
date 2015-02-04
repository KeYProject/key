package org.key_project.jmlediting.core.profile.syntax;

import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.ltk.core.refactoring.Change;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.JavaElementIdentifier;

/**
 *
 * @author David Giessing The Implementing Class provides a methods to generate
 *         a Lis of Changes for Refactoring Purposes.
 */
public interface IKeywordContentRefactorer {

   /**
    * Compiles a List of changes from the given AST based on the Object.
    *
    * @param elem
    *           The Object to refactor
    * @param contentNode
    *           The AST to traverse
    * @return List of changes for Refactoring
    */
   List<Change> refactorFieldRename(JavaElementIdentifier elem,
         IASTNode contentNode, ICompilationUnit cu);

}
