// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter.IdentityFilterEntry;

/**
 * @author jschiffl
 * This filter takes a search string and yields
 * a sequent containing only sequent formulas that 
 * match the search.
 */
public class HideSequentPrintFilter extends SearchSequentPrintFilter {

	@Override
	protected void filterSequent() {
		
		int searchFlag = 0;
	    if (searchString.toLowerCase().equals(searchString)) {
	        searchFlag = searchFlag | Pattern.CASE_INSENSITIVE | Pattern.UNICODE_CASE;
	    }
	    
	    if (!regex) {
	        // search for literal string instead of regExp
	        searchFlag = searchFlag | Pattern.LITERAL;
	    }

	    Pattern p;
	    try {
	        p = Pattern.compile(searchString.replace("\u00A0", "\u0020"), searchFlag);
	    } catch (PatternSyntaxException pse) {
	        return;
	    } catch (IllegalArgumentException iae) {
	        return;
	    }
	    
		Iterator<SequentFormula> it;
		
		antec = ImmutableSLList.<SequentPrintFilterEntry>nil();
		it = originalSequent.antecedent().iterator();
		while (it.hasNext()) {
			SequentFormula sf = it.next();
			Matcher m = p.matcher(sf.toString().replace("\u00A0", "\u0020")); //TODO toString is not sufficient here
			if (m.find()) {
				antec.append(new IdentityFilterEntry(sf));
			}
		}
		
		succ = ImmutableSLList.<SequentPrintFilterEntry>nil();
		it = originalSequent.succedent().iterator();
		while (it.hasNext()) {
			SequentFormula sf = it.next();
			Matcher m = p.matcher(sf.toString().replace("\u00A0", "\u0020")); //TODO toString is not sufficient here
			if (m.find()) {
				succ.append(new IdentityFilterEntry(sf));
			}
		}
	}
	
}
