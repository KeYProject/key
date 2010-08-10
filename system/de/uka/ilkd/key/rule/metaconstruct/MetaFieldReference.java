// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * At present, field references cannot be applied to schema variables. This
 * class can be used to allow access to a field of a schema variable w/o 
 * having to create a MetaOperator for each field. 
 * 
 * Usage:   #fieldref(sv, "field")
 * 
 * TODO make matching possible, too
 * TODO make accessible in modalities
 * TODO allow simpler access:   sv.field
 *  
 * @author mulbrich
 */
public class MetaFieldReference extends AbstractMetaOperator implements
        Location {

    private static final Logger logger =
            Logger.getLogger(MetaFieldReference.class);

    public MetaFieldReference() {
        super(new Name("#fieldref"), 2);
    }

    /**
     * calculates the resulting term.
     * 
     * @throws RuntimeException if attribute could not be found
     */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {

        try {

            Term t = term.sub(0);
            Sort sort = t.sort();
            Term attrTerm = term.sub(1);

            String attrName = Notation.StringLiteral.printStringTerm(attrTerm);

            // strip away the " "
            attrName = attrName.substring(1, attrName.length() - 1);

            // new ObjectInspector(term).setVisible(true);

            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
            ProgramVariable attr =
                    services.getJavaInfo().getAttribute(attrName, kjt);

            return termFactory.createAttributeTerm(attr, t);
        } catch (Exception e) {
            logger.error("calculating #fiedref failed", e);
            logger.debug(term.toString());
            throw new RuntimeException("calculating #fieldref failed", e);
        }
    }

    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

    public Sort sort() {
        return METASORT;
    }

}
