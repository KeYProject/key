package org.key_project.jmlediting.profile.key.test.seq;

import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqDefKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqKeyword;
import org.key_project.jmlediting.profile.key.seq.SeqPrimitiveKeyword;
import org.key_project.jmlediting.profile.key.test.KeyProfileTestUtils;

public class SeqExprTest {

   private final String textComment = " @ ghost \\seq x; \n" + " @ "
         + " @ requires x == \\seq_empty; \n"
         + " @ requires y == \\values [2 .. 5] [3..4]; \n"
         + " @ ensures x == \\seq_singleton (1); \n"
         + " @ ensures y == hallo.get() (\\seq_def int x; a;b;c); \n" + " @ \n"
         + " @ set x = \\seq_concat(\\seq_singleton(1), \\seq_empty); \n"
         + " @ ";

   @Test
   public void parseAllSeqKeywords() throws ParserException {
      final IJMLProfile keyProfile = KeyProfileTestUtils.keyProfile();
      final IJMLParser parser = keyProfile.createParser();
      final IASTNode node = parser.parse(this.textComment, 0,
            this.textComment.length());

      final List<IKeywordNode> keywordNodes = Nodes.getAllKeywords(node);
      final Set<IKeyword> allParsedKeywords = new HashSet<IKeyword>();
      for (final IKeywordNode kNode : keywordNodes) {
         allParsedKeywords.add(kNode.getKeyword());
      }

      final Set<IKeyword> expectedKeywords = new HashSet<IKeyword>();
      expectedKeywords.addAll(JMLProfileHelper.filterKeywords(keyProfile,
            SeqPrimitiveKeyword.class));
      expectedKeywords.addAll(JMLProfileHelper.filterKeywords(keyProfile,
            SeqDefKeyword.class));
      expectedKeywords.addAll(JMLProfileHelper.filterKeywords(keyProfile,
            SeqKeyword.class));

      for (final IKeyword expectedKeyword : expectedKeywords) {
         assertTrue("Parsed seq comment does not contains expected keyword "
               + expectedKeyword.getKeywords().iterator().next(),
               allParsedKeywords.contains(expectedKeyword));
      }

   }
}
