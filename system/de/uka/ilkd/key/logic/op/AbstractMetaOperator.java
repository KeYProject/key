// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import java.util.HashMap;

import de.uka.ilkd.key.explicitheap.SameField;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.metaconstruct.*;
import de.uka.ilkd.key.rule.metaconstruct.arith.*;
import de.uka.ilkd.key.util.Debug;


public abstract class AbstractMetaOperator extends AbstractSortedOperator 
                                           implements MetaOperator {

    private static HashMap<String, AbstractMetaOperator> name2metaop = 
        new HashMap<String, AbstractMetaOperator>(70);
    
    //must be first
    public static final Sort METASORT = new PrimitiveSort(new Name("Meta"));    
    
    public static final AbstractMetaOperator META_FIELDREF = new MetaFieldReference(); 

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

    public static final AbstractMetaOperator ARRAY_BASE_INSTANCE_OF = new ArrayBaseInstanceOf();

    public static final AbstractMetaOperator ARRAY_STORE_STATIC_ANALYSE = new ArrayStoreStaticAnalyse();

    public static final AbstractMetaOperator RESOLVE_QUERY = new ResolveQuery();

    public static final AbstractMetaOperator CONSTANT_VALUE = new ConstantValue();
    
    public static final AbstractMetaOperator ENUM_CONSTANT_VALUE = new EnumConstantValue();
    
    public static final AbstractMetaOperator DIVIDE_MONOMIALS = new DivideMonomials ();

    public static final AbstractMetaOperator DIVIDE_LCR_MONOMIALS = new DivideLCRMonomials ();

    public static final AbstractMetaOperator CREATE_IN_REACHABLE_STATE_PO = 
        new CreateInReachableStatePO ();
    
    public static final AbstractMetaOperator INTRODUCE_ATPRE_DEFINITIONS = new IntroAtPreDefsOp();
    
    public static final AbstractMetaOperator AT_PRE_EQUATIONS = new AtPreEquations();
            
    public static final AbstractMetaOperator META_METHOD_CALL_TO_UPDATE= new MethodCallToUpdate();
    
    public static final AbstractMetaOperator SAME_FIELD = new SameField();

    
    protected static final TermFactory termFactory = TermFactory.DEFAULT;
    protected static final TermBuilder TB = TermBuilder.DF;
    
    
    private static Sort[] createMetaSortArray(int arity) {
	Sort[] result = new Sort[arity];
	for(int i = 0; i < arity; i++) {
	    result[i] = METASORT;
	}
	return result;
    }
    
    
    protected AbstractMetaOperator(Name name, int arity, Sort sort) {
	super(name, createMetaSortArray(arity), sort);
	name2metaop.put(name.toString(), this);	
    }
    
    
   protected AbstractMetaOperator(Name name, int arity) {
	this(name, arity, METASORT);
    }


    
    public static MetaOperator name2metaop(String s) {
	return name2metaop.get(s);
    }


    /** @return String representing a logical integer literal 
     *  in decimal representation
     */
    public static String convertToDecimalString(Term term, Services services) {
      	String result = "";
	boolean neg = false;
	Operator top = term.op();
	Namespace intFunctions = services.getNamespaces().functions();
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
    
    
    @Override
    public boolean isRigid() {
	return false;
    }
    

    /** (non-Javadoc)
     * by default meta operators do not match anything 
     * @see de.uka.ilkd.key.logic.op.Operator#match(SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    @Override    
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        return null;
    }    
}
