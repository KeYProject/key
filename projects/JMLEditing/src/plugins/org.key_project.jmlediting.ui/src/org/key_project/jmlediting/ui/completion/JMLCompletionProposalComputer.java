package org.key_project.jmlediting.ui.completion;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;
import org.key_project.jmlediting.ui.extension.JMLLocator;

/**
 * An {@link IJavaCompletionProposalComputer} to support JML.
 * @author Martin Hentschel
 * @author Thomas Glaser
 */
public class JMLCompletionProposalComputer implements IJavaCompletionProposalComputer {
	@Override
	public void sessionStarted() {
	}

	@Override
	public List<ICompletionProposal> computeCompletionProposals(ContentAssistInvocationContext context, IProgressMonitor monitor) {
		List<ICompletionProposal> result = new LinkedList<ICompletionProposal>();
		try {
		   //add proposals only if Content Assist is invoked in JML Code
		   JMLLocator locator = new JMLLocator(context.getDocument());
		   if (locator.isInJMLcomment(context.getInvocationOffset())) {

		      //getCurrentProject
		      IProject currentProject = getCurrentProject();
		      
		      //Load the specific JMLProfile for the current Project.
		      IJMLProfile currentJMLProfile = JMLPreferencesHelper.getProjectActiveJMLProfile(currentProject);
		      
		      //get the prefix to filter only fitting keywords
		      String prefix = context.computeIdentifierPrefix().toString();
		      int prefixLength = prefix.length();
		      
		      //compute the offset for replacing the prefix
		      int proposalOffset = context.getInvocationOffset() - prefix.length();
		      
		      //Iterate through the supported Behaviors defined in JMLProfile
		      for (IJMLBehaviorKeyword behavior: currentJMLProfile.getSupportedBehaviors()) {
		         Set<String> keywords = behavior.getKeywords();
		         //check for all spellings
		         for (String keyword: keywords) {
		            //ignore not possible suggestions
		            if (keyword.startsWith(prefix)) {
		               result.add(new CompletionProposal(keyword, proposalOffset, prefixLength, keyword.length()));
		            }
		         }
		      }
		      //Iterate through all generic Keywords defined in JMLProfile
		      for (ISpecificationStatementKeyword generic: currentJMLProfile.getSupportedSpecificationStatementKeywords()) {
		         String keyword = generic.getKeyword();
		         //ignore not possible suggestions
		         if (keyword.startsWith(prefix)) {
		            result.add(new CompletionProposal(keyword, proposalOffset, prefixLength, keyword.length()));
		         }
		      }
		   }
		}
      catch (Exception e) {
         e.printStackTrace();
      }
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
	
   public static IProject getCurrentProject() {
      IProject project = null;
      
      IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
      IWorkbenchPage activePage = window.getActivePage();
      IEditorPart editorPart = activePage.getActiveEditor();
      IResource resource = (IResource) editorPart.getEditorInput().getAdapter(IResource.class);
      if (resource != null) {
         project = resource.getProject();
      }
      return project;
   }
}
