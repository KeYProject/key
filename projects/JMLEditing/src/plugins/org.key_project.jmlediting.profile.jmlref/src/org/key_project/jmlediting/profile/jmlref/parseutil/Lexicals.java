package org.key_project.jmlediting.profile.jmlref.parseutil;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

public class Lexicals {

   public static final int INFORMAL_DESCRIPTION = NodeTypes
         .getNewType("InformalDescription");

   public static final ParseFunction lexInformalDescr = new ParseFunction() {
      @Override
      public IASTNode parse(final String text, final int start, final int end)
            throws ParserException {
         if (start + 2 > end) {
            throw new ParserException("Expected an Informal Description", text,
                  start);
         }
         if (!(text.charAt(start) == '(' && text.charAt(start + 1) == '*')) {
            throw new ParserException("Invalid informal description start",
                  text, start);
         }
         // Scan for end, no string or escapes handles here, so its easy
         int position = start + 2;
         // +1 here because we need to have space for an additional character to
         // find *) end
         boolean foundEnd = false;
         while (position + 1 < end) {
            if (text.charAt(position) == '*'
                  && text.charAt(position + 1) == ')') {
               foundEnd = true;
               break;
            }
            position++;
         }
         if (!foundEnd) {
            throw new ParserException(
                  "Expected closing (* for informal description", text, end);
         }

         return Nodes.createNode(
               start,
               position + 2,
               INFORMAL_DESCRIPTION,
               Nodes.createString(start + 2, position,
                     text.substring(start + 2, position)));

      }

   };

}
