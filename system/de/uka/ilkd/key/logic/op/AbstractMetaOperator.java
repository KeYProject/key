// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//

package de.uka.ilkd.key.logic.op;

import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.*;
import de.uka.ilkd.key.rule.metaconstruct.arith.*;
import de.uka.ilkd.key.util.Debug;

/** 
 * this class implements the interface for
 * MetaOperators. MetaOperators are used to do complex term
 * transformation when applying a taclet. Often these transformation
 * caanot be described with the taclet scheme (or trying to do so would
 * result in a huge number of rules)
 */
public abstract class AbstractMetaOperator extends Op implements MetaOperator {

    private static HashMap<String, AbstractMetaOperator> name2metaop = 
        new HashMap<String, AbstractMetaOperator>(70);

    public static final AbstractMetaOperator META_LENGTH = new MetaLength();

    public static final AbstractMetaOperator META_ATTRIBUTE = new MetaAttribute();

    public static final AbstractMetaOperator META_CREATED = new MetaCreated();
    
    public static final AbstractMetaOperator META_NEXT_TO_CREATE = new MetaNextToCreate();


    public static final AbstractMetaOperator META_TRAINITIALIZED = new MetaTraInitialized();

    public static final AbstractMetaOperator META_TRANSIENT = new MetaTransient();

    public static final AbstractMetaOperator META_TRANSACTIONCOUNTER = 
	new MetaTransactionCounter();
    
    /** general access to nonstatic fields in classes */
    public static final AbstractMetaOperator META_FIELDREF = new MetaFieldReference(); 

    /** the shadow operator for transactions */
    public static final AbstractMetaOperator META_SHADOW = new MetaShadow();

    /** used to add integers */
    public static final AbstractMetaOperator META_ADD = new MetaAdd();

    public static final AbstractMetaOperator META_SUB = new MetaSub();

    public static final AbstractMetaOperator META_MUL = new MetaMul();

    public static final AbstractMetaOperator META_DIV = new MetaDiv();

    public static final AbstractMetaOperator META_LESS = new MetaLess();

    public static final AbstractMetaOperator META_GREATER = new MetaGreater();

    public static final AbstractMetaOperator META_LEQ = new MetaLeq();

    public static final AbstractMetaOperator META_GEQ = new MetaGeq();

    public static final AbstractMetaOperator META_EQ = new MetaEqual();

    public static final AbstractMetaOperator META_INT_AND = new MetaJavaIntAnd();

    public static final AbstractMetaOperator META_INT_OR = new MetaJavaIntOr();

    public static final AbstractMetaOperator META_INT_XOR = new MetaJavaIntXor();

    public static final AbstractMetaOperator META_INT_SHIFTRIGHT = new MetaJavaIntShiftRight();

    public static final AbstractMetaOperator META_INT_SHIFTLEFT = new MetaJavaIntShiftLeft();

    public static final AbstractMetaOperator META_INT_UNSIGNEDSHIFTRIGHT = new MetaJavaIntUnsignedShiftRight();

    public static final AbstractMetaOperator META_LONG_AND = new MetaJavaLongAnd();

    public static final AbstractMetaOperator META_LONG_OR = new MetaJavaLongOr();

    public static final AbstractMetaOperator META_LONG_XOR = new MetaJavaLongXor();

    public static final AbstractMetaOperator META_LONG_SHIFTRIGHT = new MetaJavaLongShiftRight();

    public static final AbstractMetaOperator META_LONG_SHIFTLEFT = new MetaJavaLongShiftLeft();

    public static final AbstractMetaOperator META_LONG_UNSIGNEDSHIFTRIGHT = new MetaJavaLongUnsignedShiftRight();

    public static final AbstractMetaOperator WHILE_INV_RULE = new WhileInvRule();
    
    public static final AbstractMetaOperator ENHANCEDFOR_INV_RULE = new EnhancedForInvRule();

    public static final AbstractMetaOperator INTRODUCE_NEW_ANON_UPDATE = new IntroNewAnonUpdateOp();

    public static final AbstractMetaOperator ARRAY_BASE_INSTANCE_OF = new ArrayBaseInstanceOf();

    public static final AbstractMetaOperator ARRAY_STORE_STATIC_ANALYSE = new ArrayStoreStaticAnalyse();

    public static final AbstractMetaOperator EXPAND_DYNAMIC_TYPE = new ExpandDynamicType();

    public static final AbstractMetaOperator RESOLVE_QUERY = new ResolveQuery();

    public static final AbstractMetaOperator CONSTANT_VALUE = new ConstantValue();
    
    public static final AbstractMetaOperator ENUM_CONSTANT_VALUE = new EnumConstantValue();
    
    public static final AbstractMetaOperator UNIVERSES = new Universes();

    public static final AbstractMetaOperator DIVIDE_MONOMIALS = new DivideMonomials ();

    public static final AbstractMetaOperator DIVIDE_LCR_MONOMIALS = new DivideLCRMonomials ();

    public static final AbstractMetaOperator CREATE_IN_REACHABLE_STATE_PO = 
        new CreateInReachableStatePO ();
    
    public static final AbstractMetaOperator INTRODUCE_ATPRE_DEFINITIONS = new IntroAtPreDefsOp();
    
    public static final AbstractMetaOperator AT_PRE_EQUATIONS = new AtPreEquations();
    
    public static final AbstractMetaOperator LOCATION_DEPENDENT_FUNCTION = new LocationDependentFunction();
    
    /** metaconstructs for OCL simplification */
    public static final AbstractMetaOperator METAALLSUBTYPES = new MetaAllSubtypes();
    
    /** metaconstruct for the updateCut rule*/
    public static final AbstractMetaOperator METAEQUALUPDATES = new MetaEquivalentUpdates();

    public static final AbstractMetaOperator METABOOL2LOGIC = new MetaBool2Logic();

    
    public static final Sort METASORT = new PrimitiveSort(new Name("Meta"));

    
    protected TermFactory termFactory = TermFactory.DEFAULT;

    private int arity;

    public AbstractMetaOperator(Name name, int arity) {
	super(name);
	this.arity = arity;
	name2metaop.put(name.toString(), this);
    }

    /**
     * checks whether the top level structure of the given {@link Term}
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	// a meta operator accepts almost everything
	return term.op() instanceof AbstractMetaOperator;
    }

    public static MetaOperator name2metaop(String s) {
	return name2metaop.get(s);
    }

    /**
     * determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * @param term an array of Term containing the subterms of a (potential)
     * term with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     * given substerms
     */
    public Sort sort(Term[] term) {
	return METASORT;
    }

    /** @return arity of the Operator as int */
    public int arity() {
	return arity;
    }

    /** @return String representing a logical integer literal 
     *  in decimal representation
     */
    public static String convertToDecimalString(Term term, Services services) {
      	String result = "";
	boolean neg = false;
	Operator top = term.op();
	LDT intModel = services.getTypeConverter().getIntegerLDT();	    
	Namespace intFunctions = intModel.functions();
	Operator numbers = (Operator)intFunctions.lookup(new Name("Z"));
	Operator base = (Operator)intFunctions.lookup(new Name("#"));
	Operator minus =(Operator) intFunctions.lookup(new Name("neglit"));
	
	// check whether term is really a "literal"
	if (!top.name().equals(numbers.name())){
	    Debug.out("abstractmetaoperator: Cannot convert to number:", term);
	    throw (new NumberFormatException());
	}
	term = term.sub(0);
	top = term.op();

	while (top.name().equals(minus.name())){
	    neg=!neg;
	    term = term.sub(0);
	    top = term.op();
	}

	while (! top.name().equals(base.name())){
	    result = top.name()+result;
	    term = term.sub(0);
	    top = term.op();
	}
	
	if (neg)
	    return "-"+result;
	else
	    return result;
    }
    
    public MetaOperator getParamMetaOperator(String param) {
      return null;
    }
    

    /** (non-Javadoc)
     * by default meta operators do not match anything 
     * @see de.uka.ilkd.key.logic.op.Operator#match(SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        return null;
    }
    /** calculates the resulting term. */
    public abstract Term calculate(Term term, SVInstantiations svInst, Services services);

}
