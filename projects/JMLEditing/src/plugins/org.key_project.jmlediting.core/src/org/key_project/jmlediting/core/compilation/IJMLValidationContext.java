package org.key_project.jmlediting.core.compilation;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;

public interface IJMLValidationContext {

   IASTNode getJMLNode();

   String getSrc();

   List<CommentRange> getJMLComments();
}
