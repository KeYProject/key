package org.key_project.jmlediting.core.parser.util;

import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * This class contains constant values for types of nodes parsed by
 * {@link JavaBasicsParser}.
 *
 * @author Moritz Lichter
 *
 */
public final class JavaBasicsNodeTypes {

   /**
    * no instances.
    */
   private JavaBasicsNodeTypes() {

   }

   public static final int INTEGER_LITERAL = NodeTypes
         .getNewType("IntegerLiteral");
   public static final int FLOAT_LITERAL = NodeTypes.getNewType("FloatLiteral");
   public static final int BOOLEAN_LITERAL = NodeTypes
         .getNewType("BooleanLiteral");
   public static final int CHARACTER_LITERAL = NodeTypes
         .getNewType("CharacterLiteral");
   public static final int STRING_LITERAL = NodeTypes
         .getNewType("StringLiteral");
   public static final int NULL_LITERAL = NodeTypes.getNewType("NullLiteral");

   public static final int NAME = NodeTypes.getNewType("Name");

}
