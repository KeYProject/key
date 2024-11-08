/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ldt.IntLDT;
import org.key_project.rusty.logic.Place;
import org.key_project.rusty.logic.sort.SortImpl;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.rusty.rule.metaconstruct.arith.*;

/**
 * Abstract class factoring out commonalities of typical term transformer implementations. The
 * available singletons of term transformers are kept here.
 */
public abstract class AbstractTermTransformer extends AbstractSortedOperator
        implements TermTransformer {
    // must be first
    /** The metasort sort **/
    public static final Sort METASORT = new SortImpl(new Name("Meta"));

    /** A map from String names to meta operators **/
    public static final Map<String, AbstractTermTransformer> NAME_TO_META_OP =
        new LinkedHashMap<>(17);

    public static final AbstractTermTransformer META_SHIFTRIGHT = new MetaShiftRight();
    public static final AbstractTermTransformer META_SHIFTLEFT = new MetaShiftLeft();
    public static final AbstractTermTransformer META_AND = new MetaBinaryAnd();
    public static final AbstractTermTransformer META_OR = new MetaBinaryOr();
    public static final AbstractTermTransformer META_XOR = new MetaBinaryXor();
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

    public static final AbstractTermTransformer DIVIDE_MONOMIALS = new DivideMonomials();
    public static final AbstractTermTransformer DIVIDE_LCR_MONOMIALS = new DivideLCRMonomials();

    public static final AbstractTermTransformer PV_TO_MUT_REF = new PVToMutRef();
    public static final AbstractTermTransformer CREATE_S_REF = new CreateSRef();

    protected AbstractTermTransformer(Name name, int arity, Sort sort) {
        super(name, createMetaSortArray(arity), sort, Modifier.NONE);
        NAME_TO_META_OP.put(name.toString(), this);
    }

    protected AbstractTermTransformer(Name name, int arity) {
        this(name, arity, METASORT);
    }

    private static Sort[] createMetaSortArray(int arity) {
        Sort[] result = new Sort[arity];
        Arrays.fill(result, METASORT);
        return result;
    }

    public static TermTransformer name2metaop(String s) {
        return NAME_TO_META_OP.get(s);
    }

    private static class PVToMutRef extends AbstractTermTransformer {
        public PVToMutRef() {
            super(new Name("pvToMutRef"), 1);
        }

        @Override
        public Term transform(Term term, SVInstantiations svInst, Services services) {
            var tb = services.getTermBuilder();
            return tb.mutRef(MutRef.getInstance(Place.convertToPlace(term), services));
        }
    }

    private static class CreateSRef extends AbstractTermTransformer {
        public CreateSRef() { super(new Name("createSRef"), 1); }

        @Override
        public Term transform(Term term, SVInstantiations svInst, Services services) {
            var tb = services.getTermBuilder();
            return tb.sharedRef(SharedRef.getInstance(term.sub(0).sort(), services), term.sub(0));
        }
    }

    /**
     * @return String representing a logical integer literal in decimal representation
     */
    public static String convertToDecimalString(Term term, Services services) {
        StringBuilder result = new StringBuilder();
        boolean neg = false;

        Operator top = term.op();
        IntLDT intModel = services.getLDTs().getIntLDT();
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
            // LOGGER.debug("abstractmetaoperator: Cannot convert to number: {}", term);
            throw new NumberFormatException();
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
