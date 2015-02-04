package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.MethodDeclaration;

public class MethodDeclarationFinder extends ASTVisitor {
   private final List<MethodDeclaration> decls = new ArrayList<MethodDeclaration>();

   public List<MethodDeclaration> getDecls() {
      return this.decls;
   }

   @Override
   public boolean visit(final MethodDeclaration node) {
      System.out.println("nodeStart for " + node.getName() + ": "
            + node.getStartPosition());
      this.decls.add(node);
      return super.visit(node);
   }
}