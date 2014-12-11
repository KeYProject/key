package org.key_project.jmlediting.core.profile.syntax;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * An {@link AbstractKeyword} does some default implementation for an
 * {@link IKeyword}.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractKeyword implements IKeyword {

   /**
    * A set of all supported keywords.
    */
   private final Set<String> keywords;

   /**
    * Creates a new {@link AbstractKeyword}. The list of supported keywords is
    * converted to a set, but for easier code the varargs are used in the
    * constructor,
    *
    * @param keywords
    *           all supported keywords
    */
   public AbstractKeyword(final String keyword, final String... keywords) {
      super();
      switch (keywords.length) {
      case 0:
         // Do some performance optimizations for the regular case that we have
         // only one keyword
         this.keywords = Collections.singleton(keyword);
         break;
      default:
         final HashSet<String> k = new HashSet<String>(Arrays.asList(keywords));
         k.add(keyword);
         this.keywords = Collections.unmodifiableSet(k);
      }
   }

   @Override
   public Set<String> getKeywords() {
      return this.keywords;
   }

   @Override
   public List<ICompletionProposal> createAutoProposals(final IASTNode node,
         final JavaContentAssistInvocationContext context) {
      return Collections.emptyList();
   }

}
