// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.util.Iterator;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.NewDependingOn;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Listen for rule applications, add abbreviations of skolem functions
 */
public class SkolemAbbreviator implements RuleAppListener {

    private KeYMediator mediator;

    public SkolemAbbreviator ( KeYMediator p_mediator ) {
	mediator = p_mediator;

	mediator.addRuleAppListener ( this );
    }
    
    /** invoked when a rule has been applied */
    public void ruleApplied(ProofEvent ev) {
        RuleAppInfo rai = ev.getRuleAppInfo ();

        if ( rai == null ) return;

        RuleApp ruleApp = rai.getRuleApp ();
        if ( ruleApp != null && ruleApp instanceof TacletApp ) {
            final TacletApp app = (TacletApp)ruleApp;
            final Iterator<NewDependingOn> it = app.taclet ().varsNewDependingOn ();

            while ( it.hasNext () ) {
                final SchemaVariable sv = it.next ().first ();
                if ( !sv.isSkolemTermSV () ) continue;
                final Term t = (Term)app.instantiations ().getInstantiation ( sv );

                assert t != null : "Instantiation missing, but should be there";

                if ( t.op ().arity () > 0 ) addAbbreviation ( t );
            }
        }
    }

    private void addAbbreviation (Term p_t) {
        try {            
            final String abbrev = p_t.op ().name ().toString ();
            mediator.getNotationInfo ().getAbbrevMap ().put ( p_t, abbrev, true );
        } catch ( AbbrevException e ) {
            final Logger logger = Logger.getLogger ( SkolemAbbreviator.class.getName () );
            logger.warn ( "Error occurred when trying to add "
                          + "abbreviation of skolem symbol:\n" + e );
        }
    }

}
