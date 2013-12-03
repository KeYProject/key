// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * The labeled term class is used for terms that have a label 
 * attached.
 * 
 * Two labeled terms are equal if they have equal term structure and equal annotations. In 
 * contrast the method {@link Term#equalsModRenaming(Object)} does not care about annotations and will just 
 * compare the term structure alone modula renaming.
 * 
 * @see Term
 * @see TermImpl
 */
class LabeledTermImpl extends TermImpl {

	private final ImmutableArray<TermLabel> labels;

	/**
	 * creates an instance of a labeled term.
	 * @param op the top level operator 
	 * @param subs the Term that are the subterms of this term 
	 * @param boundVars logic variables bound by the operator
	 * @param javaBlock contains the program part of the term (if any) 
	 * @param labels the terms labels (must not be null or empty)
	 */
	public LabeledTermImpl(Operator op, ImmutableArray<Term> subs,
			ImmutableArray<QuantifiableVariable> boundVars, 
			JavaBlock javaBlock,
			ImmutableArray<TermLabel> labels) {
		super(op, subs, boundVars, javaBlock);
		assert labels != null : "Term labels must not be null";
		assert !labels.isEmpty() : "There must be at least one term label";
		this.labels = labels;
	}
	
	/**
	 * {@inheritDoc}
	 */
	public boolean hasLabels() {
		return true;
	}
	
	/**
	 * returns the labels attached to this term
	 */
	@Override
	public ImmutableArray<TermLabel> getLabels() {
		return labels;
	}

	/**
	 * returns true if the given label is attached
	 * @param label the ITermLabel for which to look (must not be null)
	 * @return true iff. the label is attached to this term
	 */
	@Override
	public boolean containsLabel(TermLabel label) {
		assert label != null : "Label must not be null";
		for (TermLabel l : labels) {
			if (label.equals(l)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * {@inheritDoc}
	 */
	public boolean equals(Object o) {
		if (!(o instanceof LabeledTermImpl)) {
			return false;
		}
		final LabeledTermImpl cmp = (LabeledTermImpl) o;
		if (labels.size() == cmp.labels.size()) {
			if (!super.equals(o)) {
				return false;
			}
			for (TermLabel l : labels) { // this is not optimal, but as long as number of labels limited ok
				if (!cmp.labels.contains(l)) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	/**
	 * {@inheritDoc}
	 */
	public int hashCode() {
		return super.hashCode() * 17 + labels.hashCode();
	}

	/**
	 * {@inheritDoc}
	 */
	public String toString() {
		StringBuilder result = new StringBuilder(super.toString());
		result.append("<<");
		// as labels must not be empty at least one element exists
		result.append(labels.get(0).toString()); 
		for (int i = 1; i<labels.size();i++) {
			result.append(", \"");
			result.append(labels.get(i).toString());			
         result.append("\"");
		}		
		result.append(">>");
		return result.toString();
	}
}