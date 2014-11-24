package org.key_project.jmlediting.core.dom;

import java.util.List;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;

public interface IBehaviorSpecification extends ISpecificationCase{
  
   Visibility getVisibility();
   IJMLBehaviorKeyword getKeyword();
   List<ISpecificationStatement> getSpecificationStatements();
}
