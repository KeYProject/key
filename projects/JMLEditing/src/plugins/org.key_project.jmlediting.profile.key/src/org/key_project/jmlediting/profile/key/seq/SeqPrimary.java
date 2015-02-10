package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IJMLPrimary;

public class SeqPrimary implements IJMLPrimary {

   private SeqExpressionParser seqExprParser;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.seqExprParser.parse(text, start, end);
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      this.seqExprParser = new SeqExpressionParser(profile);
   }
}
