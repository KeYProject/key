package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.TypeDeclaration;

/**
 * An ASTVisitor to find all TypeDeclarations in an AST.
 * 
 * @author Thomas Glaser
 *
 */
public class TypeDeclarationFinder extends ASTVisitor {
   /**
    * The found Declarations.
    */
   private final List<TypeDeclaration> decls = new ArrayList<TypeDeclaration>();

   /**
    * Returns the list of TypeDeclarations in the AST.
    * 
    * @return the list or an empty List if there are no TypeDeclarations in the
    *         AST
    */
   public List<TypeDeclaration> getDecls() {
      return this.decls;
   }

   @Override
   public boolean visit(final TypeDeclaration node) {
      this.decls.add(node);
      return super.visit(node);
   }

}