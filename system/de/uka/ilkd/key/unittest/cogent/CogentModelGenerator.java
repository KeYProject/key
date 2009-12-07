// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest.cogent;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.unittest.DecProdModelGenerator;
import de.uka.ilkd.key.unittest.EquivalenceClass;
import de.uka.ilkd.key.unittest.Model;

public class CogentModelGenerator extends DecProdModelGenerator {

    private ImmutableSet<Term> locations;

    private HashMap<Term, EquivalenceClass> term2class;

    private CogentTranslation ct;

    public CogentModelGenerator(CogentTranslation ct,
	    HashMap<Term, EquivalenceClass> term2class, ImmutableSet<Term> locations) {
	this.ct = ct;
	this.term2class = term2class;
	this.locations = locations;
    }

    public Set<Model> createModels() {
	HashSet<Model> models = new HashSet<Model>();
	Model model = new Model(term2class);
	try {
	    String trans = ct.translate();
	    CogentResult response = DecisionProcedureCogent.execute(trans);
	    if (response.valid()) {
		if (response.error()) {
		    Main
			    .getInstance()
			    .mediator()
			    .popupInformationMessage(
				    "Cogent execution reports an error. Check, e.g., if cogent does execute on your machine, or if there is another bug in KeY.",
				    "Error");
		    // throw new CogentException();
		}
		return models;
	    }
	    Iterator<Term> it = locations.iterator();
	    while (it.hasNext()) {
		Term t = it.next();
		EquivalenceClass ec = term2class.get(t);
		if (ec.isInt()) {
		    model.setValue(ec, response.getValueForTerm(t, ct));
		}
	    }
	    models.add(model);
	} catch (IOException e) {
	    throw new CogentException(e);
	}
	return models;
    }
}
