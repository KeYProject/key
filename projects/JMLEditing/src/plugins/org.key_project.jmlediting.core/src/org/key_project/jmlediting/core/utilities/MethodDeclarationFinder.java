package org.key_project.jmlediting.core.utilities;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.MethodDeclaration;

/**
 * ASTVisitor for finding Method Declarations.
 * 
 * @author Thomas Glaser
 *
 */
public class MethodDeclarationFinder extends ASTVisitor {

   /**
    * The List to store the MethodDeclarations in.
    */
   private final List<MethodDeclaration> decls = new ArrayList<MethodDeclaration>();

   /**
    * Returns the List of found Method Declarations.
    * 
    * @return the List
    */
   public List<MethodDeclaration> getDecls() {
      return this.decls;
   }

   @Override
   public boolean visit(final MethodDeclaration node) {
      this.decls.add(node);
      return super.visit(node);
   }
}