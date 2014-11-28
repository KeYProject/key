package org.key_project.jmlediting.core.dom;

import java.util.List;

public interface INodeSearcher<T> {
   
   T searchNode(IASTNode node);
   IASTNode selectChild(List<IASTNode> children);

}
