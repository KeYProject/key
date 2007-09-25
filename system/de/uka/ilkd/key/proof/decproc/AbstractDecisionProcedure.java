// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Calendar;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;


/**
 * Abstract base class for decision procedure wrappers.
 * Provides common functionality for the ICS and Simplify wrappers.
 */
public abstract class AbstractDecisionProcedure {
    
    protected final Goal goal;
    protected final Constraint userConstraint;
    protected final DecisionProcedureTranslationFactory dptf;
    protected final Services services;
    protected final Node node;
    
    public AbstractDecisionProcedure(Goal goal, Constraint userConstraint,
				     DecisionProcedureTranslationFactory dptf, Services services) {
        this.goal = goal;
	this.node = goal.node();
        this.userConstraint = userConstraint;
        this.dptf = dptf;
        this.services = services;
    }

    public AbstractDecisionProcedure(Node node, Constraint userConstraint,
				     DecisionProcedureTranslationFactory dptf, 
				     Services services) {
        this.goal = null;
	this.node = node;
        this.userConstraint = userConstraint;
        this.dptf = dptf;
        this.services = services;
    }
    
    /**
     * the method responsible for making various calls to the underlying
     * decision procedure with different Constraints
     * @param lightWeight true iff only quantifier free formulas shall be
     * considered.
     */
    public DecisionProcedureResult run (boolean lightWeight) {
        ConstraintSet constraintSet = new ConstraintSet ( node.sequent(), 
							  userConstraint );
        Constraint internalConstraint = constraintSet.chooseConstraintSet ();
        DecisionProcedureResult res = runInternal (constraintSet, lightWeight);
        if (res.getResult ()) {
            return res;
        } else {
            if (constraintSet.addUserConstraint ( userConstraint )) {
                return runInternal ( constraintSet, lightWeight );
            } else {
                return res;
            }
        }

    }      

    /**
     * the method responsible for making various calls to the underlying
     * decision procedure with different Constraints
     */
    public DecisionProcedureResult run (){
	return run(false);
    }

    /**
     * Invokes the actual decision procedure. This method is responsible for
     * translating to the syntax of the external tool, as well as passing this
     * as input to the tool and capturing its.
     */
    protected abstract DecisionProcedureResult runInternal (
            ConstraintSet constraintSet , boolean lightWeight);

    private static String toStringLeadingZeros ( int n, int width ) {
        String rv = "" + n;
        while ( rv.length() < width ) {
            rv = "0" + rv;
        }
        return rv;
    }
    
    /**
     * Constructs a date for use in log filenames.
     */
    protected static String getCurrentDateString () {
        Calendar c = Calendar.getInstance();
        StringBuffer sb = new StringBuffer();
        String dateSeparator = "-";
        String dateTimeSeparator = "_";
        sb.append(toStringLeadingZeros(c.get(Calendar.YEAR), 4))
          .append( dateSeparator )
          .append(toStringLeadingZeros(c.get(Calendar.MONTH) + 1, 2))
          .append( dateSeparator )
          .append(toStringLeadingZeros(c.get(Calendar.DATE), 2))
          .append( dateTimeSeparator )
          .append(toStringLeadingZeros(c.get(Calendar.HOUR_OF_DAY), 2) +"h" )
          .append(toStringLeadingZeros(c.get(Calendar.MINUTE), 2) + "m" )
          .append(toStringLeadingZeros(c.get(Calendar.SECOND), 2) + "s" )
          .append('.')
          .append(toStringLeadingZeros(c.get(Calendar.MILLISECOND), 2));
        return sb.toString();
    }

    /** Read the input until end of file and return contents in a
     * single string containing all line breaks. */
    protected static String read ( InputStream in ) throws IOException {
        String lineSeparator = System.getProperty("line.separator");
        BufferedReader reader = new BufferedReader
            (new InputStreamReader(in));
        StringBuffer sb = new StringBuffer();
        String line;
        while ((line = reader.readLine()) != null) {
            sb.append(line).append(lineSeparator);
        }
        return sb.toString();
    }

}
