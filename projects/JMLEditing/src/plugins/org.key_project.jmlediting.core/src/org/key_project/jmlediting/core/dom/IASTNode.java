package org.key_project.jmlediting.core.dom;

import java.util.List;

public interface IASTNode {
   
   int getStartOffset();
   int getEndOffset();
   
   int getType();
   
   List<IASTNode> getChildren();
   
   <T> T serach(INodeSearcher<T> searcher);
   
}
