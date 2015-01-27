package org.key_project.jmlediting.core.profile.syntax;

import java.util.List;

import org.eclipse.ltk.core.refactoring.Change;
import org.key_project.jmlediting.core.dom.IASTNode;

public interface IKeywordContentRefactorer {

   public List<Change> refactorFieldRename(Object o, IASTNode contentNode);

}
