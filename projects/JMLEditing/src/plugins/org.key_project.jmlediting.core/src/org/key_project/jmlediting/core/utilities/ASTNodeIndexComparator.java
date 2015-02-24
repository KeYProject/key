package org.key_project.jmlediting.core.utilities;

import java.util.Comparator;

import org.eclipse.jdt.core.dom.ASTNode;

/**
 * Compares two ASTNodes based on their start Index
 * 
 * @author David Giessing
 *
 */
public class ASTNodeIndexComparator implements Comparator<ASTNode> {

   @Override
   public int compare(final ASTNode arg0, final ASTNode arg1) {
      if (arg0.getStartPosition() < arg1.getStartPosition()) {
         return -1;
      }
      else if (arg0.getStartPosition() < arg1.getStartPosition()) {
         return 0;
      }
      else {
         return 1;
      }
   }

}
