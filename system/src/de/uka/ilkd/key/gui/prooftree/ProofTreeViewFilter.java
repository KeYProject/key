package de.uka.ilkd.key.gui.prooftree;

import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

/**
 * Filters for the proof tree view.
 * @author bruns
 *
 */
public abstract class ProofTreeViewFilter {
	
	public final static ProofTreeViewFilter HIDE_INTERMEDIATE = new HideIntermediateFilter();
	public final static ProofTreeViewFilter HIDE_CLOSED_SUBTREES = new HideClosedSubtreesFilter();
	public final static ProofTreeViewFilter ONLY_INTERACTIVE = new OnlyInteractiveFilter();
	
	public final static ProofTreeViewFilter[] ALL = 
		new ProofTreeViewFilter[] {HIDE_INTERMEDIATE, HIDE_CLOSED_SUBTREES, ONLY_INTERACTIVE};
	
	public abstract String name();
	public abstract boolean isActive ();
	abstract void setActive(boolean active);

	private static class HideIntermediateFilter extends ProofTreeViewFilter {

		@Override
		public boolean isActive() {
			return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getHideIntermediateProofsteps();
		}

		@Override
		void setActive(boolean active) {
			ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideIntermediateProofsteps(active);	
		}

		@Override
		public String name() {
			return "Hide Intermediate Proofsteps";
		}
	}
	
	private static class OnlyInteractiveFilter extends ProofTreeViewFilter {

		@Override
		public boolean isActive() {
			return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getHideAutomodeProofsteps();
		}

		@Override
		void setActive(boolean active) {
			ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideAutomodeProofsteps(active);
		}

		@Override
		public String name() {
			return "Hide Non-interactive Proofsteps";
		}
		
	}
	
	private static class HideClosedSubtreesFilter extends ProofTreeViewFilter {

		@Override
		public boolean isActive() {
			return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getHideClosedSubtrees();
		}

		@Override
		void setActive(boolean active) {
			ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHideClosedSubtrees(active);
		}

		@Override
		public String name() {
			return "Hide Closed Subtrees";
		}
		
	}
}
