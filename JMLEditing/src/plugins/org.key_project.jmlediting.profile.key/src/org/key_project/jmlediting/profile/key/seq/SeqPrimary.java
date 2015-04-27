package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;

/**
 * The seq primary which adds support for seq primaries in JML expression.
 *
 * @author Moritz Lichter
 *
 */
public class SeqPrimary implements IJMLPrimary {

   /**
    * Parse for primaries.
    */
   private SeqPrimaryParser seqExprParser;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.seqExprParser.parse(text, start, end);
   }

   @Override
   public void setProfile(final IJMLExpressionProfile profile) {
      this.seqExprParser = new SeqPrimaryParser(profile);
   }
}
