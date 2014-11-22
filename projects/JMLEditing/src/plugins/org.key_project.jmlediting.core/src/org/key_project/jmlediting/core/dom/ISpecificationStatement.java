package org.key_project.jmlediting.core.dom;

import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public interface ISpecificationStatement extends IASTNode {
   
   ISpecificationStatementKeyword getKeyword();
   String getContent();

}
