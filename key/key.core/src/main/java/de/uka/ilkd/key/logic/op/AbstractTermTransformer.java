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

package de.uka.ilkd.key.logic.op;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.metaconstruct.*;
import de.uka.ilkd.key.rule.metaconstruct.arith.*;
import de.uka.ilkd.key.util.Debug;

/**
 * Abstract class factoring out commonalities of typical term transformer implementations.
 * The available singletons of term transformers are kept here.
 */
public abstract class AbstractTermTransformer extends AbstractSortedOperator
        implements TermTransformer {

    // must be first
    /** The metasort sort **/
    public static final Sort METASORT = new SortImpl(new Name("Meta"));

    /** A map from String names to meta operators **/
    public static final Map<String, AbstractTermTransformer> NAME_TO_META_OP =
            new LinkedHashMap<String, AbstractTermTransformer>(70);

    // TODO: This seems to be better handled using a ServiceLoader

    public static final AbstractTermTransformer META_SHIFTRIGHT = new MetaShiftRight();

    public static final AbstractTermTransformer META_SHIFTLEFT = new MetaShiftLeft();

    public static final AbstractTermTransformer META_AND = new MetaBinaryAnd();

    public static final AbstractTermTransformer META_OR = new MetaBinaryOr();

    public static final AbstractTermTransformer META_XOR = new MetaBinaryXOr();

    public static final AbstractTermTransformer META_ADD = new MetaAdd();

    public static final AbstractTermTransformer META_SUB = new MetaSub();

    public static final AbstractTermTransformer META_MUL = new MetaMul();

    public static final AbstractTermTransformer META_DIV = new MetaDiv();

    public static final AbstractTermTransformer META_POW = new MetaPow();

    public static final AbstractTermTransformer META_LESS = new MetaLess();

    public static final AbstractTermTransformer META_GREATER = new MetaGreater();

    public static final AbstractTermTransformer META_LEQ = new MetaLeq();

    public static final AbstractTermTransformer META_GEQ = new MetaGeq();

    public static final AbstractTermTransformer META_EQ = new MetaEqual();

    public static final AbstractTermTransformer ARRAY_BASE_INSTANCE_OF = new ArrayBaseInstanceOf();

    public static final AbstractTermTransformer CONSTANT_VALUE = new ConstantValue();

    public static final AbstractTermTransformer ENUM_CONSTANT_VALUE = new EnumConstantValue();

    public static final AbstractTermTransformer DIVIDE_MONOMIALS = new DivideMonomials();

    public static final AbstractTermTransformer DIVIDE_LCR_MONOMIALS = new DivideLCRMonomials();

    public static final AbstractTermTransformer INTRODUCE_ATPRE_DEFINITIONS = new IntroAtPreDefsOp();

    public static final AbstractTermTransformer CREATE_LOCAL_ANON_UPDATE = new CreateLocalAnonUpdate();
    public static final AbstractTermTransformer CREATE_HEAP_ANON_UPDATE = new CreateHeapAnonUpdate();
    public static final AbstractTermTransformer CREATE_BEFORE_LOOP_UPDATE = new CreateBeforeLoopUpdate();
    public static final AbstractTermTransformer CREATE_FRAME_COND = new CreateFrameCond();
    public static final AbstractTermTransformer CREATE_WELLFORMED_COND = new CreateWellformedCond();

    public static final AbstractTermTransformer MEMBER_PV_TO_FIELD = new MemberPVToField();

    /** The add-cast term transformer **/
    public static final AbstractTermTransformer ADD_CAST = new AddCast();

    public static final AbstractTermTransformer EXPAND_QUERIES = new ExpandQueriesMetaConstruct();

    /** Transformer producing condition for equality of observer terms */
    public static final AbstractTermTransformer OBSERVER_EQUALITY =
            new ObserverEqualityMetaConstruct();

    private static Sort[] createMetaSortArray(int arity) {
        Sort[] result = new Sort[arity];
        for (int i = 0; i < arity; i++) {
            result[i] = METASORT;
        }
        return result;
    }

    protected AbstractTermTransformer(Name name, int arity, Sort sort) {
        super(name, createMetaSortArray(arity), sort, false);
        NAME_TO_META_OP.put(name.toString(), this);
    }

    protected AbstractTermTransformer(Name name, int arity) {
        this(name, arity, METASORT);
    }

    public static TermTransformer name2metaop(String s) {
        return NAME_TO_META_OP.get(s);
    }

    /** @return String representing a logical integer literal
     *  in decimal representation
     */
    public static String convertToDecimalString(Term term, Services services) {
        StringBuilder result = new StringBuilder();
        boolean neg = false;

        Operator top = term.op();
        IntegerLDT intModel = services.getTypeConverter().getIntegerLDT();
        final Operator numbers = intModel.getNumberSymbol();
        final Operator base = intModel.getNumberTerminator();
        final Operator minus = intModel.getNegativeNumberSign();
        // check whether term is really a "literal"

        // skip any updates that have snuck in (int lits are rigid)
        while (top == UpdateApplication.UPDATE_APPLICATION) {
            term = term.sub(1);
            top = term.op();
        }

        if (top != numbers) {
            Debug.out("abstractmetaoperator: Cannot convert to number:", term);
            throw (new NumberFormatException());
        }

        term = term.sub(0);
        top = term.op();

        // skip any updates that have snuck in (int lits are rigid)
        while (top == UpdateApplication.UPDATE_APPLICATION) {
            term = term.sub(1);
            top = term.op();
        }

        while (top == minus) {
            neg = !neg;
            term = term.sub(0);
            top = term.op();

            // skip any updates that have snuck in (int lits are rigid)
            while (top == UpdateApplication.UPDATE_APPLICATION) {
                term = term.sub(1);
                top = term.op();
            }
        }

        while (top != base) {
            result.insert(0, top.name());
            term = term.sub(0);
            top = term.op();

            // skip any updates that have snuck in (int lits are rigid)
            while (top == UpdateApplication.UPDATE_APPLICATION) {
                term = term.sub(1);
                top = term.op();
            }
        }

        if (neg) {
            result.insert(0, "-");
        }

        return result.toString();
    }
}
