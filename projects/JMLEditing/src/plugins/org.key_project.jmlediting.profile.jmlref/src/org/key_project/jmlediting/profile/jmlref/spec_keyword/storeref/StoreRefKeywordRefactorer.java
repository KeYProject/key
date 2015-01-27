package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.util.Collections;
import java.util.List;

import org.eclipse.ltk.core.refactoring.Change;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.profile.syntax.IKeywordContentRefactorer;

public class StoreRefKeywordRefactorer implements IKeywordContentRefactorer {

   @Override
   public List<Change> refactorFieldRename(final Object o,
         final IASTNode contentNode) {
      return Collections.emptyList();
   }

}
