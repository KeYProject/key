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


import de.uka.ilkd.asmkey.logic.AsmLemma;
import de.uka.ilkd.asmkey.logic.AsmRule;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;


/** Implementation of DeclarationEnvironment that forwards (delegates)
 * all queries to another DeclarationEnvironment.
 *
 * @author Hubert Schmid
 */

class DelegateDeclarationEnvironment extends DelegateTermEnvironment implements DeclarationEnvironment {

    /** The environment to which all queries are forwarded. */
    private final DeclarationEnvironment env;


    DelegateDeclarationEnvironment(DeclarationEnvironment env) {
        super(env);
        this.env = env;
    }

    public void addMetaOperator(MetaOperator op) throws EnvironmentException {
	env.addMetaOperator(op);
    }

    public void addSort(Sort sort) throws EnvironmentException {
        env.addSort(sort);
    }

    public void addSchemaVariable(SchemaVariable v) throws EnvironmentException {
        env.addSchemaVariable(v);
    }

    public void addOperator(Operator op) throws EnvironmentException {
        env.addOperator(op);
    }

    public void replaceOperator(Operator op) throws EnvironmentException {
	env.replaceOperator(op);
    }

    public void addRuleSet(RuleSet h) throws EnvironmentException {
        env.addRuleSet(h);
    }

    public RuleSet getRuleSet(Name id) throws EnvironmentException {
        return env.getRuleSet(id);
    }

    public void addTaclet(Taclet t) throws EnvironmentException {
        env.addTaclet(t);
    }

    public void addRule(AsmRule p) throws EnvironmentException {
        env.addRule(p);
    }
    
    public void addLemma(AsmLemma l) throws EnvironmentException {
	env.addLemma(l);
    }
    
    public Name name() {
	return env.name();
    }

}
