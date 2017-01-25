package de.uka.ilkd.key.pp;

public abstract class SearchSequentPrintFilter extends SequentPrintFilter {
	
	protected String searchString;
	protected boolean regex;
	protected LogicPrinter lp;

	public void setSearchString(String searchString) {
		this.searchString = searchString;
	}

}
