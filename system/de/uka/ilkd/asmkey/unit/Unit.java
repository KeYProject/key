// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;


import de.uka.ilkd.asmkey.logic.AsmLemma;
import de.uka.ilkd.asmkey.logic.AsmRule;
import de.uka.ilkd.asmkey.logic.TimedNonRigidFunction;
import de.uka.ilkd.asmkey.logic.sort.SequenceSort;
import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.parser.env.AbbreviationMap;
import de.uka.ilkd.asmkey.parser.env.DeclarationEnvironment;
import de.uka.ilkd.asmkey.parser.env.EnvironmentException;
import de.uka.ilkd.asmkey.proof.AsmProof;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.SetSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.SetAsListOfTaclet;
import de.uka.ilkd.key.rule.SetOfTaclet;
import de.uka.ilkd.key.rule.Taclet;


/**
 * This class serves as Vertex in the UnitGraph that is constructed 
 * by the UnitManager; there is some info stored in it like its namespace,
 * import information, status of loading, etc...
 */
public class Unit implements Named, DeclarationEnvironment {


    /**
     * A unit can have different status:
     * - NEW: the unit was just created and is still empty;
     * - UNLOADED: the unit contains all metainformation, but has not loaded its Namespace yet;
     * - LOADED: the unit has loaded its Namespace;
     * - ERROR: there is a an error with this unit: e.g. it cannot load because of a syntax error.
     */
    public static final int NEW = 0;
    public static final int UNLOADED = 1;
    public static final int LOADED = 2;
    public static final int ERROR = 3;

    /** The name of the unit  */
    private Name name;

    /** the loading status */
    int status;

    /** when attached to a graph */
    UnitGraph graph;

    /** the KeYMediator, to update the notation info if necessary */
    private final KeYMediator mediator;

    /** The import informations for each imported namespace.
     * used when a name is not found in the current namespace.
     */
    private ImportInfo[] imports;

    /** the AstUnit used for this unit: as we parse
     * in two passes. it is usefull to have the astUnit
     * attached the unit as the Unit is constructed step by step
     * @see UnitManager
     */
    private transient AstUnit astUnit;

    private Unit(Name name, AstUnit astUnit) {
	super();
	this.name = name;
	this.astUnit = astUnit;
	this.status = Unit.NEW;
	this.mediator = null;
	
	metaOps = new UnitNamespace(this) {
		UnitNamespace getNamespaceForUnit(Unit unit) {
		    return unit.metaOpNS();
		}
		
		int type() {
		    return RestrictedSymbol.META_OPERATOR;
		}
	    };
	sorts = new SortUnitNamespace(this);
	vars = new UnitNamespace(this) {
		UnitNamespace getNamespaceForUnit(Unit unit) {
		    return unit.varNS();
		}

		int type() {
		    return RestrictedSymbol.SCHEMA_VARIABLE;
		}
	    };
	ops = new FunctionUnitNamespace(this);
	
	rules = new UnitNamespace(this) {
		UnitNamespace getNamespaceForUnit(Unit unit) {
		    return unit.ruleNS();
		}

		int type() {
		    return RestrictedSymbol.ASMRULE;
		}
	    };
	
	ruleSets = new UnitNamespace(this) {
		UnitNamespace getNamespaceForUnit(Unit unit) {
		    return unit.ruleSetNS();
		}
		
		int type() {
		    return RestrictedSymbol.HEURISTIC;
		}
	    };
	taclets = new UnitNamespace(this) {
		UnitNamespace getNamespaceForUnit(Unit unit) {
		    return unit.tacletNS();
		}

		int type() {
		    return RestrictedSymbol.TACLET;
		}
	    };
	lemmas = new UnitNamespace(this) {
		UnitNamespace getNamespaceForUnit(Unit unit) {
		    return unit.lemmaNS();
		}

		int type() {
		    return RestrictedSymbol.PROPOSITION;
		}
	    };
	this.choices = new Namespace();
	this.pvars = new Namespace();
        this.abbreviations = null;
    }

    public Unit(Name name) {
	this(name, null);
    }

    Unit(String name) {
	this(new Name(name), null);
    }

    public Unit(AstUnit astUnit) {
	this(new Name(astUnit.getUnitId().getText()), astUnit);
    }

    /* name and string */

    public Name name() {
	return name;
    }

    public String toString() {
	return name.toString();
    }

    /* status */

    public int status() {
	return status;
    }

    void setStatus(int status) {
	this.status = status;
    }
    
    /* graph */
    
    protected UnitGraph graph() {
	return this.graph;
    }

    void setGraph(UnitGraph graph) {
	this.graph = graph;
    }

    /* import info */
    
    public ImportInfo[] getImportInfos() {
	return imports;
    }

    void setImportInfos(ImportInfo[] imports) {
	this.imports = imports;
    }

    Object getRestrictedSymbol(RestrictedSymbol symbol) throws UnitException {
	UnitNamespace ns = getNSForType(symbol.type());
	return ns.lookup(symbol.symbol());
    }

    boolean containsRestrictedSymbol(RestrictedSymbol symbol) throws UnitException {
	return getRestrictedSymbol(symbol) != null;
    }

    public UnitNamespace getNSForType(int type) throws UnitException {
	switch (type) {
	case RestrictedSymbol.META_OPERATOR:
	    return metaOpNS();
	case RestrictedSymbol.SORT:
	    return sortNS();
	case RestrictedSymbol.SCHEMA_VARIABLE:
	    return varNS();
	case RestrictedSymbol.FUNCTION:
	    return funcNS();
	case RestrictedSymbol.ASMRULE:
	    return ruleNS();
	case RestrictedSymbol.TACLET:
	    return tacletNS();
	case RestrictedSymbol.PROPOSITION:
	    return lemmaNS();
	case RestrictedSymbol.HEURISTIC:
	    return ruleSetNS();
	}
	throw new UnitException("There is no Namespace for this type: type=" + type);
    }

    /* --- parsing --- */

    public AstUnit astUnit() {
	return astUnit;
    }
    
    /** when the parsing is finished, there is no more use
     * of the AstUnit, we can therefore discard it
     */
    public void voidAstUnit() {
	astUnit = null;
    }

    /* --- implementation of the DeclarationEnvironment interface --- */

    /* we have first Namespaces for each kind of operators.
     * they will be used to implements the DeclarationEnvironment interface
     * and super interface. */
    
    /** Meta operators. Mapping from {@link Name} to {@link
     * MetaOperator}. */
    private final UnitNamespace metaOps;

    /** Declared sorts. Mapping from {@link Name} to {@link
     * Sort}. */
    private final UnitNamespace sorts;

    /** Schema variables. Mapping from {@link Name} to {@link
     * SchemaVariable}. */
    private final UnitNamespace vars;

    /** Operations, functions and predications. Mapping from {@link
     * Name} to {@link Operator}. */
    private final UnitNamespace ops;

    /** Named asm rules (procedures). Mapping from {@link Name} to
     * {@link AsmRule}. */
    private final UnitNamespace rules;

    /** Declared heuristics. Mapping from {@link Name} to {@link
     * Heuristic}. */
    private final UnitNamespace ruleSets;

    /** Declared taclets. Mapping from {@link Name} (taclet name) to
     * {@link Taclet}. */
    private final UnitNamespace taclets;

    /** Declared lemmas. Mapping from {@link Name} (lemma name) to
     * {@link AsmLemma} */
    private final UnitNamespace lemmas;

    /** Choices, not used yet
     */
    private final Namespace choices;

    /** Program variables, not used
     */
    private final Namespace pvars;
    
    /** Abbreviations. */
    private final AbbreviationMap abbreviations;

    public UnitNamespace metaOpNS() {
	return metaOps;
    }

    public UnitNamespace sortNS() {
	return sorts;
    }

    public UnitNamespace funcNS() {
	return ops;
    }

    public UnitNamespace varNS () {
	return vars;
    }

    public UnitNamespace ruleSetNS() {
	return ruleSets;
    }

    public Namespace choiceNS() {
	return choices;
    }

    public Namespace progVarNS() {
	return pvars;
    }

    public UnitNamespace lemmaNS() {
	return lemmas;
    }

    public UnitNamespace tacletNS() {
	return taclets;
    }

    public UnitNamespace ruleNS() {
	return rules;
    }

    private boolean existsFunctionLike(Name id) {
	return containsMetaOp(id) || containsSchemaVariable(id) ||
	    containsOperator(id);
    }

    private boolean existsPropLike(Name id) {
	return containsTaclet(id) || containsLemma(id);
    }

    public boolean containsMetaOp(Name id) {
        return metaOps.lookup(id) != null;
    }

    public MetaOperator getMetaOp(Name id) throws EnvironmentException {
        return (MetaOperator) lookup("Meta operator", id, metaOps);
    }

    public void addMetaOperator(MetaOperator mop) throws EnvironmentException {
	Name id = mop.name();
	if (existsFunctionLike(id)) {
	    throw new EnvironmentException("Cannot add MetaOperator " + id +
					   ": a function-like symbol is already defined.");
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
        if (existsFunctionLike(id)) {
            throw new EnvironmentException("Cannot add SchemaVariable " + id +
					   ": a function-like symbol is already defined.");
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
        if (existsFunctionLike(id)) {
            throw new EnvironmentException("Cannot add Operator " + id +
					   ": a function-like is already defined.");
        } else {
            ops.add(op);
	    if (op instanceof NonRigidFunction) {
		//accessDFInfoFactory.register(op.name());
		//updateDFInfoFactory.register(op.name());
	    }
        }
    }
    
    public void replaceOperator(Operator op) throws EnvironmentException {
	Name id = op.name();
	if (containsOperator(id)) {
	    ops.add(op);
	} else {
	    throw new EnvironmentException("Cannot replace Operator " + id +
					   ": the operator does not already exists.");
	}
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

    /** Returns all declared (and initial) rule sets. */
    public ListOfNamed getRuleSets() {
        return ruleSets.allElements();
    }

    public boolean containsTaclet(Name name) {
	return taclets.lookup(name) != null;
    }

    public void addTaclet(Taclet t) throws EnvironmentException {
	Name id = t.name();
        if (existsPropLike(id)) {
            throw new EnvironmentException("A Taclet/Lemma " + id + " is already defined.");
        } else {
            taclets.add(t);
        }
    }

    public Taclet getTaclet(Name name) throws EnvironmentException {
	return (Taclet) lookup("Taclet", name, taclets);
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

    public boolean containsLemma(Name name) {
	return lemmas.lookup(name) != null;
    }
    
    public void addLemma(AsmLemma lemma) throws EnvironmentException {
	Name id = lemma.name();
	if(existsPropLike(id)) {
	    throw new EnvironmentException("A Taclet/Lemma " + id + " is already defined.");
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

    /** PropLike */
    public Named getPropLike(Name id) {
	try {
	    if (containsLemma(id)) {
		return getLemma(id);
	    } else if(containsTaclet(id)) {
		return getTaclet(id);
	    } else {
		return null;
	    }
	} catch (EnvironmentException e) {
	    throw new RuntimeException("As we check existence before getting, we should" +
				       "never throw this exception: " + e + ".");
	}
    }

    public boolean isParsingDerivedFunction() {
	return false;
    }

    /** Create a namespace from a collection a Named objects. The
     * elements of 'c' have to be of type {@link Named}. */
   //  private static Namespace toNamespace(Collection c) {
// 	if (c == null) return null;

//         Namespace ns = new Namespace();
//         for (Iterator i = c.iterator(); i.hasNext();) {
//             ns.add((Named) i.next());
//         }
//         return ns;
//     }
    
    
    public NamespaceSet getEnvAsNamespaceSet() {
       return new NamespaceSet(
          vars,
          ops, // XXX: filter functions
          sorts,
          ruleSets,
	  new Namespace(), new Namespace());
    }
    /*
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
	}*/


    /** Returns the element with the name 'id' from the namespace. Throws an
     * EnvironmentException with the text name, if no such element
     * exists.
     *
     * @throws EnvironmentException if no such element exists.
     */
    private static Named lookup(String name, Name id, UnitNamespace ns) throws EnvironmentException {
	Named n = ns.lookup(id);
        if (n != null) {
            return n;
        } else {
            throw new EnvironmentException(name + " " + id + " not found.");
        }
    }


    /* --- taclet registration ---*/

    /**
     * This method registers all the taclets of this unit, including
     * taclets from the units it depends on. The actual registration
     * is done the method {@link #registerTaclets}.
     */
    public void registerAllTaclets(ProofEnvironment proofEnvironment) {
	for(int i=0; i<imports.length; i++) {
	    imports[i].unit().registerTaclets(proofEnvironment);
	}
	registerTaclets(proofEnvironment);
    }

    /**
     * This method registers the own taclets of this unit; it asks
     * the unit/storage managers to find out the justification
     * for each taclet.
     */
    void registerTaclets(ProofEnvironment proofEnvironment) {
	IteratorOfNamed it = tacletNS().elements().iterator();
	while (it.hasNext()) {
	    Taclet tac = (Taclet) it.next();
	    proofEnvironment.registerRule(tac, 
					  AxiomJustification.INSTANCE);
	}
    }

    /* --- proof + problem part --- */
    public Problem constructProblem(final Name name)
	throws ProofInputException {
	final Named prop = getPropLike(name);
	if (prop != null) {
	    if (prop instanceof Taclet) {
		throw new ProofInputException("Taclet proving not yet supported.");
	    } else if(prop instanceof AsmLemma) {
		return new Problem(this) {
			public ProofAggregate getPO() {
			    if (initConfig == null) {
				throw new IllegalStateException("Unit#Problem: InitConfig not set.");
			    } else {
				AsmProof proof = new AsmProof
				    (name.toString(), 
				     ((AsmLemma) prop).getFormula(),
				     "lemma",
				     initConfig.createTacletIndex(),
				     initConfig.createBuiltInRuleIndex(),
				     initConfig.getServices(),
				     unit());
				return new SingleProof(proof, name.toString());
			    }
			}

			public String name() {
			    return name.toString();
			}

			public void initJavaModelSettings(String classPath) {}
		    };
	    } else {
		throw new ProofInputException
		    ("The named element " + name +
		     " is neither a taclet nor a proposition.");
	    }
	} else {
	    throw new ProofInputException
		("No prop/taclet exists with this name: " + name + ".");
	}
    }

    /**
     * Different MetaOperator and Conditions needs to have a list
     * of the "current" dynamic function
     */
    public ListOfNonRigidFunction getNonRigidFunctions() {
	ListOfNonRigidFunction result = SLListOfNonRigidFunction.EMPTY_LIST;
	for(int i=0; i<imports.length; i++) {
	    result = imports[i].unit().ownNonRigidFunctions(result);
	}
	result = ownNonRigidFunctions(result);
	return result;
    }

    ListOfNonRigidFunction ownNonRigidFunctions(ListOfNonRigidFunction result) {
	IteratorOfNamed it = funcNS().elements().iterator();
	while(it.hasNext()) {
	    Named f = it.next();
	    if (f instanceof NonRigidFunction && !(f instanceof TimedNonRigidFunction)) {
		result = result.append((NonRigidFunction) f);
	    }
	}
	return result;
    }
    
}

