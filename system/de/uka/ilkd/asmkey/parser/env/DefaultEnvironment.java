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


import java.util.Collection;
import java.util.Iterator;

import de.uka.ilkd.asmkey.logic.AsmLemma;
import de.uka.ilkd.asmkey.logic.AsmRule;
import de.uka.ilkd.asmkey.logic.dfinfo.DFException;
import de.uka.ilkd.asmkey.logic.dfinfo.DFInfo;
import de.uka.ilkd.asmkey.logic.dfinfo.DFInfoFactory;
import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.asmkey.logic.sort.SequenceSort;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.SetSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.SetAsListOfTaclet;
import de.uka.ilkd.key.rule.SetOfTaclet;
import de.uka.ilkd.key.rule.Taclet;



/** Implementation for SortEnvironment, TermEnvironment and
 * DeclarationEnvironment.
 *
 * @author Hubert Schmid
 */

public class DefaultEnvironment implements DeclarationEnvironment {

    /** Returns the element with the name 'id' from the map. Throws an
     * EnvironmentException with the text name, if no such element
     * exists.
     *
     * @throws EnvironmentException if no such element exists.
     */
    private static Named lookup(String name, Name id, Namespace ns) throws EnvironmentException {
	Named n = ns.lookup(id);
        if (n != null) {
            return ns.lookup(id);
        } else {
            throw new EnvironmentException(name + " " + id + " not found.");
        }
    }


    /** Meta operators. Mapping from {@link String} to {@link
     * MetaOperator}. */
    private final Namespace metaOps;

    /** Declared sorts. Mapping from {@link String} to {@link
     * Sort}. */
    private final Namespace sorts;

    /** Schema variables. Mapping from {@link String} to {@link
     * SchemaVariable}. */
    private final Namespace vars;

    /** Operations, functions and predications. Mapping from {@link
     * String} to {@link Operator}. */
    private final Namespace ops;

    /** Named asm rules (procedures). Mapping from {@link String} to
     * {@link AsmRule}. */
    private final Namespace rules;

    /** Declared heuristics. Mapping from {@link String} to {@link
     * Heuristic}. */
    private final Namespace ruleSets;

    /** Declared taclets. Mapping from {@link String} (taclet name) to
     * {@link Taclet}. */
    private final Namespace taclets;

    /** Declared lemmas. Mapping from {@link String} (lemma name) to
     * {@link AsmLemma} */
    private final Namespace lemmas;

    /** Choices, not used yet
     */
    private final Namespace choices;

    /** Program variables, not used
     */
    private final Namespace pvars;

    /** Abbreviations. */
    private final AbbreviationMap abbreviations;

    /** for registering the DFInfo's for access properties. */
    private final DFInfoFactory accessDFInfoFactory;

    /** for registering the DFInfo's for update properties */
    private final DFInfoFactory updateDFInfoFactory;


    /** Create an empty environment. */
    public DefaultEnvironment() {
        this(null, null, null, null, null, null, null, null, null, null, null);
    }

    /** Create an empty environment with the given meta operators. */
    public DefaultEnvironment(Collection metaOps, NamespaceSet n) {
        this(toNamespace(metaOps),
	     n.sorts(),
	     n.variables(),
	     n.functions(), null,
	     n.ruleSets(), null, null,
	     n.choices(),
	     n.programVariables(), null);
    }

    /** Creates an environment with the given meta operators, sorts,
     * vars, operators (functions, predicates), named asm rules
     * (procedures), heuristics, taclets and abbreviations. Each
     * argument may be null. */
    public DefaultEnvironment(Namespace metaOps,
                              Namespace sorts,
                              Namespace vars,
                              Namespace ops,
                              Namespace rules,
                              Namespace ruleSets,
                              Namespace taclets,
			      Namespace lemmas,
			      Namespace choices,
			      Namespace pvars,
                              AbbreviationMap abbreviations) {
        this.metaOps = new Namespace(metaOps);
        this.sorts = new Namespace(sorts);
        this.vars = new Namespace(vars);
        this.ops = new Namespace(ops);
        this.rules = new Namespace(rules);
        this.ruleSets = new Namespace(ruleSets);
        this.taclets = new Namespace(taclets);
	this.lemmas = new Namespace(lemmas);
	this.choices = new Namespace(choices);
	this.pvars = new Namespace(pvars);
        this.abbreviations = abbreviations;
	accessDFInfoFactory = new DFInfoFactory();
	updateDFInfoFactory = new DFInfoFactory();
	this.sorts.add(PrimitiveSort.ASMRULE);
    }

    public Namespace metaOpNS() {
	return metaOps;
    }

    public Namespace sortNS() {
	return sorts;
    }

    public Namespace funcNS() {
	return ops;
    }

    public Namespace varNS () {
	return vars;
    }

    public Namespace ruleSetNS() {
	return ruleSets;
    }

    public Namespace choiceNS() {
	return choices;
    }

    public Namespace progVarNS() {
	return pvars;
    }

    public Namespace lemmaNS() {
	return lemmas;
    }

    public Namespace tacletNS() {
	return taclets;
    }

    public Namespace ruleNS() {
	return rules;
    }

    public boolean containsMetaOp(Name id) {
        return metaOps.lookup(id) != null;
    }

    public MetaOperator getMetaOp(Name id) throws EnvironmentException {
        return (MetaOperator) lookup("Meta operator", id, metaOps);
    }

    public void addMetaOperator(MetaOperator mop) throws EnvironmentException {
	Name id = mop.name();
	if (getMetaOp(id) != null) {
	    throw new EnvironmentException("MetaOperator with name " + id +
					   " is already defined.");
	} else {
	    metaOps.add(mop);
	}
    }

    public Sort getSort(Name id) throws EnvironmentException {
        return (Sort) lookup("Sort", id, sorts);
    }

    public void addSort(Sort sort) throws EnvironmentException {
	Name id = sort.name();
        if (sorts.lookup(id) != null) {
            throw new EnvironmentException("Sort " + id + " is already defined.");
        } else {
            sorts.add(sort);

	    if (sort instanceof SetSort) { 
		// add the specific operators and notation for this sort.
		//SortDependingAsmOperator.putSetSymbols((SetSort) sort, this, mediator);
	    } else if (sort instanceof SequenceSort) {
		// add the specific operators and notation for this sort
		((SequenceSort) sort).addDefinedSymbols(ops, sorts);
	    }
        }
    }

    /** Returns all declared (and initial) sorts. */
    public ListOfNamed getSorts() {
        return sorts.allElements();
    }

    public boolean containsSchemaVariable(Name id) {
        return vars.lookup(id) != null;
    }

    public SchemaVariable getSchemaVariable(Name id) throws EnvironmentException {
        return (SchemaVariable) lookup("Schema variable", id, vars);
    }

    /** Returns all declared (and initial) schema variables. */
    public ListOfNamed getSchemaVariables() {
        return vars.allElements();
    }

    public void addSchemaVariable(SchemaVariable sv) throws EnvironmentException {
	Name id = sv.name();
        if (vars.lookup(id) != null) {
            throw new EnvironmentException("SchemaVariable " + id + " is already defined.");
        } else {
            vars.add(sv);
        }
    }

    public boolean containsOperator(Name id) {
	return ops.lookup(id) != null;
    }

    public Operator getOperator(Name id) throws EnvironmentException {
        return (Operator) lookup("Operator", id, ops);
    }

    public void addOperator(Operator op) throws EnvironmentException {
	Name id = op.name();
        if (ops.lookup(id) != null) {
            throw new EnvironmentException("Operator " + id + " is already defined.");
        } else {
            ops.add(op);
	    if (op instanceof NonRigidFunction) {
		accessDFInfoFactory.register(op.name());
		updateDFInfoFactory.register(op.name());
	    }
        }
    }

    public void replaceOperator(Operator op) throws EnvironmentException {
	throw new EnvironmentException("replaceOperator: operation not supported");
    }

    /** Returns all declared (and initial) operators. */
    public ListOfNamed getOperators() {
        return ops.allElements();
    }

    public AsmRule getRule(Name id) throws EnvironmentException {
        return (AsmRule) lookup("Procedure", id, rules);
    }

    public void addRule(AsmRule p) throws EnvironmentException {
	Name id = p.name();
        if (rules.lookup(id) != null) {
            throw new EnvironmentException("Rule " + id + " is already defined.");
        } else {
            rules.add(p);
        }
    }

    /** Returns all declared procedures (named ASM rules). */
    public ListOfNamed getRules() {
        return rules.allElements();
    }

    public RuleSet getRuleSet(Name id) throws EnvironmentException {
	return (RuleSet) lookup("Rule Set", id, ruleSets);
    }

    public void addRuleSet(RuleSet h) throws EnvironmentException {
	Name id = h.name();
        if (ruleSets.lookup(id) != null) {
            throw new EnvironmentException("Rule Set " + id + " is already defined.");
        } else {
            ruleSets.add(h);
        }
    }

    /** Returns all declared (and initial) heuristics. */
    public ListOfNamed getHeuristics() {
        return ruleSets.allElements();
    }

    public void addTaclet(Taclet t) throws EnvironmentException {
	Name id = t.name();
        if (taclets.lookup(id) != null) {
            throw new EnvironmentException("Taclet " + id + " is already defined.");
        } else {
            taclets.add(t);
        }
    }

    /** Returns all declared (and initial) taclets. */
    public ListOfNamed getTaclets() {
        return taclets.allElements();
    }

    /** Return the set of all taclets */
    public SetOfTaclet getSetOfTaclet() {
	IteratorOfNamed it = taclets.allElements().iterator();
	Taclet t;
	SetOfTaclet s = SetAsListOfTaclet.EMPTY_SET;
	
	while (it.hasNext()) {
	    t = (Taclet) it.next();
	    s = s.add(t);
	}
	return s;
    }

    public Term getAbbreviatedTerm(String name) throws EnvironmentException {
        if (abbreviations.containsAbbreviation(name)) {
            return abbreviations.getTerm(name);
        } else {
            throw new EnvironmentException("abbreviation " + name + " not found.");
        }
    }
    
    public void addLemma(AsmLemma lemma) throws EnvironmentException {
	Name id = lemma.name();
	if(lemmas.lookup(id)!= null) {
	    throw new EnvironmentException("Lemma " + id + " is already defined.");
	} else {
	    lemmas.add(lemma);
	}
    }

    /** Returns all declared lemmas. */
    public ListOfNamed getLemmas() {
	return lemmas.allElements();
    }

    public AsmLemma getLemma(Name id) throws EnvironmentException {
	return (AsmLemma) lookup("Lemma", id, lemmas);
    }

    public boolean isParsingDerivedFunction() {
	return false;
    }
    
    /** Create a namespace from a collection a Named objects. The
     * elements of 'c' have to be of type {@link Named}. */
    private static Namespace toNamespace(Collection c) {
	if (c == null) return null;

        Namespace ns = new Namespace();
        for (Iterator i = c.iterator(); i.hasNext();) {
            ns.add((Named) i.next());
        }
        return ns;
    }
    
    
    public NamespaceSet getEnvAsNamespaceSet() {
       return new NamespaceSet(
          vars,
          ops, // XXX: filter functions
          sorts,
          ruleSets,
	  new Namespace(), new Namespace());
    }

    public DFInfo getAccessDFInfo(ListOfName dfs) throws EnvironmentException {
	try {
	    return accessDFInfoFactory.getDFInfo(dfs);
	} catch (DFException e) {
	    throw new EnvironmentException("DFException: " + e.getMessage());
	}
    }

    public DFInfo getUpdateDFInfo(ListOfName dfs) throws EnvironmentException {
	try {
	    return updateDFInfoFactory.getDFInfo(dfs);
	} catch (DFException e) {
	    throw new EnvironmentException("DFException: " + e.getMessage());
	}
    }


    public Name name() {
	return new Name("");
    }

}
