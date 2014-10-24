package org.key_project.jmlediting.ui.completion;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;

/**
 * An {@link IJavaCompletionProposalComputer} to support JML.
 * @author Martin Hentschel
 */
public class JMLCompletionProposalComputer implements IJavaCompletionProposalComputer {
	@Override
	public void sessionStarted() {
	}

	@Override
	public List<ICompletionProposal> computeCompletionProposals(ContentAssistInvocationContext context, IProgressMonitor monitor) {
		List<ICompletionProposal> result = new LinkedList<ICompletionProposal>();
		String proposal = "accessible";
		result.add(new CompletionProposal(proposal, context.getInvocationOffset(), 0, proposal.length()));
		proposal = "also";
		result.add(new CompletionProposal(proposal, context.getInvocationOffset(), 0, proposal.length()));
		return result;
	}

	@Override
	public List<IContextInformation> computeContextInformation(ContentAssistInvocationContext context, IProgressMonitor monitor) {
		return Collections.emptyList();
	}

	@Override
	public String getErrorMessage() {
		return null;
	}

	@Override
	public void sessionEnded() {
	}
}
