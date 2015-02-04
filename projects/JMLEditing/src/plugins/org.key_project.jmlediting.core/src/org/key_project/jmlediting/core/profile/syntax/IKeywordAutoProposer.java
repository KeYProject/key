package org.key_project.jmlediting.core.profile.syntax;

import java.util.List;

import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * The {@link IKeywordAutoProposer} makes proposals for the content of a
 * keyword.
 *
 * @author Moritz Lichter
 *
 */
public interface IKeywordAutoProposer {

   /**
    * Calculates autoproposals for this keyword. This method is allowed to be
    * invoked on {@link IASTNode} with {@link NodeTypes#KEYWORD_CONTENT} type
    * only if the invocation offset of the given context is in this node and
    * this node is a parse result of the content of this keyword.
    *
    * @param node
    *           the node of the JML code parsed for which autoproposals are
    *           asked
    * @param context
    *           the invocation context for calculating proposals
    * @return a non null list of proposals, might be empty. if null, the
    *         proposer rejects to make proposals and indicated that toplevel
    *         keywords should be proposed
    */
   List<ICompletionProposal> createAutoProposals(IASTNode node,
         JavaContentAssistInvocationContext context);

}
