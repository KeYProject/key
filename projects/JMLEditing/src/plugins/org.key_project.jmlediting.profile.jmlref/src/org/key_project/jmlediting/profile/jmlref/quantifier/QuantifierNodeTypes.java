package org.key_project.jmlediting.profile.jmlref.quantifier;

import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * This class contains node types for the AST of quantifiers.
 *
 * @author Moritz Lichter
 *
 */
public final class QuantifierNodeTypes {

   /**
    * No instantiations.
    */
   private QuantifierNodeTypes() {

   }

   public static final int QUANTIFIER_PREDICATE = NodeTypes
         .getNewType("QuantifierPredicate");

   public static final int QUANTIFIED_EXPRESSION = NodeTypes
         .getNewType("QuantifiedExpression");

}
