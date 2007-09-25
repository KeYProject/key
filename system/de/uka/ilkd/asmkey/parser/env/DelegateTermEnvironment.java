// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.env;


import de.uka.ilkd.asmkey.logic.AsmRule;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;


/** Implementation of TermEnvironment that forwards (delegates) all
 * queries to another TermEnvironment.
 *
 * @author Hubert Schmid
 */

class DelegateTermEnvironment implements TermEnvironment {

    /** The environment to which all queries are forwarded. */
    private final TermEnvironment env;


    DelegateTermEnvironment(TermEnvironment env) {
        this.env = env;
    }


    public boolean containsMetaOp(Name id) {
        return env.containsMetaOp(id);
    }

    public MetaOperator getMetaOp(Name id) throws EnvironmentException {
        return env.getMetaOp(id);
    }

    public Sort getSort(Name id) throws EnvironmentException {
        return env.getSort(id);
    }

    public boolean containsSchemaVariable(Name id) {
        return env.containsSchemaVariable(id);
    }

    public SchemaVariable getSchemaVariable(Name id) throws EnvironmentException {
        return env.getSchemaVariable(id);
    }

    public boolean containsOperator(Name id) {
	return env.containsOperator(id);
    }

    public Operator getOperator(Name id) throws EnvironmentException {
        return env.getOperator(id);
    }

    public AsmRule getRule(Name id) throws EnvironmentException {
        return env.getRule(id);
    }

    public Term getAbbreviatedTerm(String name) throws EnvironmentException {
        return env.getAbbreviatedTerm(name);
    }

    public boolean isParsingDerivedFunction() {
	return env.isParsingDerivedFunction();
    }

}
