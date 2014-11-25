package org.key_project.jmlediting.core.dom;

import java.util.List;

public interface IMethodSpecification extends IASTNode {
   
   boolean isExtendingSpecification();
   
   List<ISpecificationCase> getSpecificationCases();

}
