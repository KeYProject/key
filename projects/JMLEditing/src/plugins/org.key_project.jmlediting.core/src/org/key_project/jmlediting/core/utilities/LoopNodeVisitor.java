package org.key_project.jmlediting.core.utilities;

import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.WhileStatement;

public class LoopNodeVisitor extends ASTVisitor {
   List<ASTNode> loopNodes = Collections.emptyList();

   public List<ASTNode> getLoopNodes() {
      return this.loopNodes;
   }

   @Override
   public boolean visit(final DoStatement node) {
      this.loopNodes.add(node);
      return super.visit(node);
   }

   @Override
   public boolean visit(final WhileStatement node) {
      this.loopNodes.add(node);
      return super.visit(node);
   }

   @Override
   public boolean visit(final ForStatement node) {
      this.loopNodes.add(node);
      return super.visit(node);
   }
}
