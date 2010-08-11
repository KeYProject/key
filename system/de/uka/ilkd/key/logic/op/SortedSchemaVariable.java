// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/**
 * This class represents the root of a schema variable hierarchy to be express
 * termstructures that match on logical terms. Schema variables are used in
 * Taclets where they act as placeholders for other TermSymbols. The TermSymbols
 * a SchemaVariable is allowed to match is specified by their type and sort. If
 * a match fits these conditions can be checked using the method
 * isCompatible(TermSymbol t)
 */
public abstract class SortedSchemaVariable extends SchemaVariableAdapter
        implements ParsableVariable, QuantifiableVariable, Location {

    /**
     * creates a new SchemaVariable. That is used as placeholder for TermSymbols
     * of a certain type.
     * 
     * @param name
     *            the Name of the SchemaVariable
     * @param matchType
     *            Class representing the type of symbols that can be matched
     * @param sort
     *            the Sort of the SchemaVariable and the matched type
     * @param listSV
     *            a boolean which is true iff the schemavariable is allowed to
     *            match a list of syntactical elements
     */
    protected SortedSchemaVariable(Name name, Class matchType, Sort sort,
            boolean listSV) {
        super(name, matchType, sort, listSV);
    }

    /**
     * tries to add the pair <tt>(this,pe)</tt> to the match conditions. If
     * possible the resulting match conditions are returned, otherwise
     * <tt>null</tt>. Such an addition can fail, e.g. if already a pair
     * <tt>(this,x)</tt> exists where <tt>x<>pe</tt>
     */
    protected MatchConditions addInstantiation(ProgramElement pe,
            MatchConditions matchCond, Services services) {

        final SVInstantiations instantiations = matchCond.getInstantiations();
        final SVSubstitute inMap = (SVSubstitute) instantiations
                .getInstantiation(this);

        if (inMap == null) {            
            try {
                return matchCond
                        .setInstantiations(instantiations.add(this, pe));
            } catch (IllegalInstantiationException e) {
                Debug
                        .out("Exception thrown by class Taclet at setInstantiations");
            }
        } else {
            Object peForCompare = pe;
            if (inMap instanceof Term) {
                try {
                    peForCompare = services.getTypeConverter()
                            .convertToLogicElement(
                                    pe,
                                    matchCond.getInstantiations()
                                            .getExecutionContext());                    
                } catch (RuntimeException re) {
                    Debug.out("Cannot convert program element to term.", this,
                            pe);
                    return null;
                }
            } 
            if (inMap.equals(peForCompare)) {
                return matchCond;
            }
        }
        Debug.out("FAILED. Illegal Instantiation.", this, pe);
        return null;
    }

    /**
     * tries to add the pair <tt>(this,term)</tt> to the match conditions. If
     * successful the resulting conditions are returned, otherwise null. Failure
     * is possible e.g. if this schemavariable has been already matched to a
     * term <tt>t2</tt> which is not unifiable with the given term.
     */
    protected MatchConditions addInstantiation(Term term,
            MatchConditions matchCond, Services services) {

        if (this.isRigid() && !term.isRigid()) {
            Debug.out("FAILED. Illegal Instantiation");
            return null;
        }      
        
        final SVInstantiations inst = matchCond.getInstantiations();

        final Term t = inst.getTermInstantiation(this, inst
                .getExecutionContext(), services);
        if (t != null) {
            final Constraint c = matchCond.getConstraint().unify(t, term,
                    services);
            if (!c.isSatisfiable()) {
                Debug.out(
                        "FAILED. Adding instantiations leads to unsatisfiable"
                                + " constraint.", this, term);
                return null; // FAILED;
            } else {
                return matchCond.setConstraint(c);
            }
        }

        try {           
            return matchCond.setInstantiations(inst.add(this, term));
        } catch (IllegalInstantiationException e) {
            Debug.out("FAILED. Exception thrown at sorted schema variable", e);
        }

        Debug.out("FAILED. Illegal Instantiation");
        return null;
    }

    /**
     * @return true if the schemavariable has the strict modifier which forces
     *         the instantiation to have exact the same sort as the
     *         schemavariable (or if the sv is of generic sort - the
     *         instantiation of the generic sort)
     */
    public boolean isStrict() {
        return true;
    }

    /**
     * checks if this schemavariable matches element <code>subst</code> with
     * respect to the given conditions and returns the resulting match
     * conditions (or null if the match is not possible)
     * 
     * @param subst
     *            the SVSubstitute to be matched
     * @param mc
     *            the MatchConditions posing restrictions on the variables to be
     *            matched
     * @param services
     *            the Services with additional information about the context
     *            (e.g. type hierarchy)
     * @return the resulting MatchConditions
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        if (subst instanceof Term) {
            return addInstantiation((Term) subst, mc, services);
        }
        // overwritten in variable sv to match logic variables
        Debug.out("FAILED. Schemavariable of this kind only match terms.");
        return null;
    }

    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

}
