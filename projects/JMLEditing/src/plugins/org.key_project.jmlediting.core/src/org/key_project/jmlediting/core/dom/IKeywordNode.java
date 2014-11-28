package org.key_project.jmlediting.core.dom;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public interface IKeywordNode extends IASTNode {
   
   IKeyword getKeyword();
   String getKeywordInstance();

}
