package org.key_project.jmlediting.core.profile.syntax;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;

/**
 * The {@link EmptyKeywordParser} implements an parser for an keyword which does
 * not expect anything after the keyword.
 *
 * @author Moritz Lichter
 *
 */
public final class EmptyKeywordParser implements IKeywordParser {

   /**
    * A shared instance for all, because the parser is stateless.
    */
   private static final EmptyKeywordParser INSTANCE = new EmptyKeywordParser();

   /**
    * Retunrs an instance of the {@link EmptyKeywordParser}.
    *
    * @return an instance
    */
   public static EmptyKeywordParser getInstance() {
      return INSTANCE;
   }

   /**
    * No public instantiations.
    */
   private EmptyKeywordParser() {
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return null;
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
   }

}
