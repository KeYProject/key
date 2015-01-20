package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.TypeDeclaration;

public class TypeDeclarationFinder extends ASTVisitor {
   private final List<TypeDeclaration> decls = new ArrayList<TypeDeclaration>();

   public List<TypeDeclaration> getDecls() {
      return this.decls;
   }

   @Override
   public boolean visit(final TypeDeclaration node) {
      this.decls.add(node);
      return super.visit(node);
   }
}