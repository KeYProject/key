// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.Vector;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SortException;

public class ApplyTacletDialogModel {
	
    /** the model used for the instantiation of the if-sequent */
    private IfChoiceModel[] ifChoiceModel;
    private static final IfChoiceModel[] EMPTY_IF_CHOICES = new IfChoiceModel [ 0 ];
    /** the model used for the instantiation of the schemavariables */
    private TacletInstantiationsTableModel tableModel;

    /** 
     * the application of the Taclet of which this model is used to
     * complete the instantiations of the schemavariables and/or
     * if-sequent
     */
    private TacletApp app;
    
    /** the sequent the application above is applied */
    private Sequent seq;

    /** listeners of this model */
    private Vector listeners = new Vector();
    /** the change event that is sent */
    private final ModelEvent changeEvent = new ModelEvent(this);

    /** namespace of variables */
    private NamespaceSet nss;
    private Services services ;
    private Constraint userConstraint;
    private AbbrevMap scm;
    private Proof proof;
  
    /**
     * create new data model for the apply Taclet dialog wrapping a combo box
     * model and a table model
     */
    public ApplyTacletDialogModel(TacletApp app, Sequent seq,
				  Services services,
				  Constraint userConstraint,
				  NamespaceSet nss, AbbrevMap scm,
				  Goal goal) {
	this.app = app;
	this.seq = seq;
	this.services = services;
	this.userConstraint = userConstraint;
	this.nss = nss;
	this.scm = scm;
	this.proof = goal.proof();
	initIfChoiceModels();

	tableModel =
	    new TacletInstantiationsTableModel(app, services, nss, scm, goal);
    }

    public void addModelChangeListener(ModelChangeListener l) {
	listeners.add(l);
    }

    public void removeModelChangeListener(ModelChangeListener l) {
	listeners.remove(l);
    }
	
    public IfChoiceModel ifChoiceModel(int i) {
	return ifChoiceModel[i];
    }

    public int ifChoiceModelCount() {
	return ifChoiceModel.length;
    }

    public TacletInstantiationsTableModel tableModel() {
	return tableModel;
    }

    public TacletApp application() {
	return app;
    }

    public Taclet taclet() {
	return app.taclet();
    }

    public TacletApp tacletApp() {
	return app;
    }


    public Proof proof() {
	return proof;
    }

    public Term ifFma(int i) {
	return ifChoiceModel(i).ifFma();
    }

    private void initIfChoiceModels() {
 	Sequent ifseq   = taclet().ifSequent();
	int     asize   = ifseq.antecedent().size();
	int     size    = asize + ifseq.succedent().size();

	if ( size > 0 ) {
	    ListOfIfFormulaInstantiation antecCand =
		IfFormulaInstSeq.createList ( seq, true );
	    ListOfIfFormulaInstantiation succCand  =
		IfFormulaInstSeq.createList ( seq, false );

	    IteratorOfConstrainedFormula it        = ifseq.iterator();
	    Term                         ifFma;
	    MatchConditions              matchCond = app.matchConditions ();

	    ifChoiceModel                          = new IfChoiceModel[size];

	    for (int i=0; i<size; i++) {
		ifFma            = it.next ().formula ();
		ifChoiceModel[i] = 
		    new IfChoiceModel ( ifFma,
					taclet ().matchIf ( ( i < asize ?
							      antecCand.iterator () :
							      succCand .iterator () ),
							    ifFma,
							    matchCond,
							    services,
							    userConstraint ).getFormulas (),
					services, nss, scm);
	    }
	} else
	    ifChoiceModel = EMPTY_IF_CHOICES;
    }



    private TacletApp createTacletAppFromIfs(TacletApp tacletApp)
	throws IfMismatchException,
	       SVInstantiationParserException,
	       MissingInstantiationException,
	       SortMismatchException {

	ListOfIfFormulaInstantiation instList = SLListOfIfFormulaInstantiation.EMPTY_LIST;

	int i = ifChoiceModel.length;
	while ( i-- != 0 ) {
	    instList = instList.prepend ( ifChoiceModel[i].getSelection (i) );
	}

	try {
	    tacletApp = tacletApp.setIfFormulaInstantiations
		( instList, services, userConstraint );
	} catch ( SortException e ) {
	    throw new SortMismatchException ( "'\\assumes'-sequent", null, 0, 0 );
	}

	if ( tacletApp == null ) {
 	    throw new IfMismatchException
		("Mismatch of '\\assumes'-formulas.\n"+
		 "Reasons may be: ambigous instantiation "+
		 "of schemavariables or unsatisfiable constraints.");
	}

	return tacletApp;
    }

    public String getStatusString() {
	TacletApp rapp = app;
        
        if (rapp == null) {
            return "Rule is not applicable."; 
        }
                
	try {	    
	    rapp = createTacletApp();
	} catch (SVInstantiationException ime) {
            return "Rule is not applicable.\n Detail:" + 
            ime.getMessage();
	}  catch (IllegalInstantiationException iie) {
            return "Rule is not applicable.\n Detail:" + 
            iie.getMessage();
        } catch(de.uka.ilkd.key.util.ExceptionHandlerException e){        
	    services.getExceptionHandler().clear();
	    return "Rule is not applicable.\n Detail:" + 
	    e.getCause().getMessage();
	}
       	
	if ( rapp.sufficientlyComplete () )
	    return "Instantiation is OK.";
	else
	    return "Instantiations are incomplete."; 
	
    }

    public TacletApp createTacletApp() throws SVInstantiationException {
	return createTacletAppFromIfs(tableModel.createTacletAppFromVarInsts());
    }
    
    
    private void informListenerAboutModelChange() {
	for (int i = 0; i < listeners.size(); i++) {
	    if (listeners.get(i) != null) {
		((ModelChangeListener)listeners.get(i)).modelChanged(changeEvent);
	    }
	}
    }

    /** sets the manual if-input */
    public void setManualInput(int i, String s) {
	ifChoiceModel(i).setInput(s);
	informListenerAboutModelChange();
    }

    /**
     * replaces the TacletApp of this ApplyTacletDialogModel by an TacletApp
     * where all name conflicts are resolved and thus the parser is enabled
     * to accept variables from the context or the prefix of the Taclet.
     *
     */
    public void prepareUnmatchedInstantiation() {
	app = app.prepareUserInstantiation();	
    }

    public Namespace programVariables() {
        return nss.programVariables();
    }

}
