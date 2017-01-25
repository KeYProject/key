package de.uka.ilkd.key.pp;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Sequent;

public class SearchSequentPrintFilter extends SequentPrintFilter {
	
	private String searchString;

	@Override
	public Sequent getOriginalSequent() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Sequent getFilteredSequent() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableList<SequentPrintFilterEntry> getFilteredAntec() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ImmutableList<SequentPrintFilterEntry> getFilteredSucc() {
		// TODO Auto-generated method stub
		return null;
	}

	private String getSearchString() {
		return searchString;
	}

	private void setSearchString(String searchString) {
		this.searchString = searchString;
	}

}
