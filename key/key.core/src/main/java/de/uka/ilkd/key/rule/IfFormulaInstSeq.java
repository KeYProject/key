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

package de.uka.ilkd.key.rule;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;

/**
 * Instantiation of an if-formula that is a formula of an existing
 * sequent.
 */

public class IfFormulaInstSeq implements IfFormulaInstantiation {

    /**
     * Sequent and formula
     */
    private final Sequent            seq;
    private final boolean antec;	// formula is in antecedent?
    private final SequentFormula cf;

    public IfFormulaInstSeq(Sequent p_seq, boolean antec, SequentFormula p_cf ) {
        seq = p_seq;
        this.antec = antec;
        cf  = p_cf;
    }


    public IfFormulaInstSeq(Sequent seq, int formulaNr ) {
        this(seq, seq.numberInAntec(formulaNr), seq.getFormulabyNr(formulaNr));
    }


    /**
     * @return the cf this is pointing to
     */
    @Override
    public SequentFormula getConstrainedFormula () {
        return cf;
    }

    /**
     * Create a list with all formulas of a given semisequent
     */
    private static ImmutableList<IfFormulaInstantiation> createListHelp(Sequent     p_s,
            boolean antec ) {
        ImmutableList<IfFormulaInstantiation> res = ImmutableSLList.<IfFormulaInstantiation>nil();
        Iterator<SequentFormula>  it;
        if (antec) {
            it = p_s.antecedent().iterator ();
        } else {
            it = p_s.succedent().iterator ();
        }
        while ( it.hasNext () ) {
            res = res.prepend(new IfFormulaInstSeq(p_s, antec, it.next()));
        }

        return res;
    }

    public static ImmutableList<IfFormulaInstantiation> createList(Sequent p_s,
            boolean antec, Services services) {
        final IfFormulaInstantiationCache cache = services.getCaches().getIfFormulaInstantiationCache();
        final Semisequent semi = antec ? p_s.antecedent() : p_s.succedent();
        
        ImmutableList<IfFormulaInstantiation> val = cache.get(antec, semi);
        
        if (val == null) {
            val  = createListHelp(p_s, antec);
            cache.put(antec, semi, val);
        }
        
        return val;
    }

    @Override
    public String toString () {
        return toString(null);
    }

    @Override
    public String toString (Services services) {
        return OutputStreamProofSaver.printAnything(cf.formula(), services);
    }

    @Override
    public boolean equals(Object p_obj) {
        if ( ! ( p_obj instanceof IfFormulaInstSeq ) ) {
            return false;
        }
        final IfFormulaInstSeq other = (IfFormulaInstSeq)p_obj;
        return seq == other.seq
                && cf == other.cf
                && antec == other.antec;
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + seq.hashCode ();
        result = 37 * result + cf.hashCode ();
        result = 37 * result + ( antec ? 0 : 1 );
        return result;
    }

    public boolean inAntec() {
        return antec;
    }

    private volatile PosInOccurrence pioCache = null;

    public PosInOccurrence toPosInOccurrence () {
        if (pioCache == null) {
            PosInOccurrence localPioCache = 
                    new PosInOccurrence ( cf,
                            PosInTerm.getTopLevel(),
                            antec );
            pioCache = localPioCache;
        }
        return pioCache;
    }

}