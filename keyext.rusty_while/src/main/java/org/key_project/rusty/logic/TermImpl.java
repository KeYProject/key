/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.concurrent.atomic.AtomicInteger;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.Strings;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

// TODO: Basically everything here can be moved tpo ncore.
class TermImpl implements Term {
    /**
     * A static empty list of terms used for memory reasons.
     */
    private static final ImmutableArray<Term> EMPTY_TERM_LIST = new ImmutableArray<>();

    /**
     * A static empty list of quantifiable variables used for memory reasons.
     */
    private static final ImmutableArray<QuantifiableVariable> EMPTY_VAR_LIST =
        new ImmutableArray<>();

    private static final AtomicInteger serialNumberCounter = new AtomicInteger();
    private final int serialNumber = serialNumberCounter.incrementAndGet();

    // content
    private final Operator op;
    private final ImmutableArray<Term> subs;
    private final ImmutableArray<QuantifiableVariable> boundVars;

    private Sort sort;
    private int depth = -1;

    private enum ThreeValuedTruth {
        TRUE, FALSE, UNKNOWN
    }

    /**
     * A cached value for computing the term's rigidness.
     */
    private ThreeValuedTruth rigid = ThreeValuedTruth.UNKNOWN;
    private ThreeValuedTruth containsCodeBlockRecursive = ThreeValuedTruth.UNKNOWN;
    private ImmutableSet<QuantifiableVariable> freeVars = null;

    /**
     * Constructs a term for the given operator, with the given sub terms, bounded variables and (if
     * applicable) the code block on this term.
     *
     * @param op the operator of the term, e.g., some arithmetic operation
     * @param subs the sub terms of the constructed term (whose type is constrained by the used
     *        operator)
     * @param boundVars the bounded variables (if applicable), e.g., for quantifiers
     */
    public TermImpl(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars) {
        assert op != null;
        assert subs != null;
        this.op = op;
        this.subs = subs.isEmpty() ? EMPTY_TERM_LIST : subs;
        this.boundVars = boundVars == null ? EMPTY_VAR_LIST : boundVars;
    }

    private ImmutableSet<QuantifiableVariable> determineFreeVars() {
        ImmutableSet<QuantifiableVariable> localFreeVars =
            DefaultImmutableSet.nil();

        if (op instanceof QuantifiableVariable) {
            localFreeVars = localFreeVars.add((QuantifiableVariable) op);
        }
        for (int i = 0, ar = arity(); i < ar; i++) {
            ImmutableSet<QuantifiableVariable> subFreeVars =
                (ImmutableSet<QuantifiableVariable>) sub(i).freeVars();
            for (int j = 0, sz = varsBoundHere(i).size(); j < sz; j++) {
                subFreeVars = subFreeVars.remove(varsBoundHere(i).get(j));
            }
            localFreeVars = localFreeVars.union(subFreeVars);
        }
        return localFreeVars;
    }

    @Override
    public Operator op() {
        return op;
    }


    @Override
    public <T> T op(Class<T> opClass) throws IllegalArgumentException {
        if (!opClass.isInstance(op)) {
            throw new IllegalArgumentException("Operator does not match the expected type:\n"
                + "Operator type was: " + op.getClass() + "\n" + "Expected type was: " + opClass);
        }
        return opClass.cast(op);
    }

    @Override
    public ImmutableArray<Term> subs() {
        return subs;
    }


    @Override
    public Term sub(int nr) {
        return subs.get(nr);
    }


    @Override
    public ImmutableArray<QuantifiableVariable> boundVars() {
        return boundVars;
    }


    @Override
    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n) {
        return op.bindVarsAt(n) ? boundVars : EMPTY_VAR_LIST;
    }

    @Override
    public int arity() {
        return op.arity();
    }

    @Override
    public Sort sort() {
        if (sort == null) {
            Sort[] sorts = new Sort[subs.size()];
            for (int i = 0; i < sorts.length; i++) {
                sorts[i] = subs.get(i).sort();
            }
            sort = op.sort(sorts);
        }
        return sort;
    }

    @Override
    public int depth() {
        if (depth == -1) {
            int localDepth = -1;
            for (int i = 0, n = arity(); i < n; i++) {
                final int subTermDepth = sub(i).depth();
                if (subTermDepth > depth) {
                    localDepth = subTermDepth;
                }
            }
            ++localDepth;
            depth = localDepth;
        }
        return depth;
    }

    @Override
    public boolean isRigid() {
        if (rigid == ThreeValuedTruth.UNKNOWN) {
            if (!op.isRigid()) {
                rigid = ThreeValuedTruth.FALSE;
            } else {
                ThreeValuedTruth localIsRigid = ThreeValuedTruth.TRUE;
                for (int i = 0, n = arity(); i < n; i++) {
                    if (!sub(i).isRigid()) {
                        localIsRigid = ThreeValuedTruth.FALSE;
                        break;
                    }
                }
                rigid = localIsRigid;
            }
        }

        return rigid == ThreeValuedTruth.TRUE;
    }

    @Override
    public ImmutableSet<QuantifiableVariable> freeVars() {
        if (freeVars == null) {
            freeVars = determineFreeVars();
        }
        return freeVars;
    }

    @Override
    public int serialNumber() {
        return serialNumber;
    }

    @Override
    public void execPostOrder(Visitor visitor) {
        visitor.subtreeEntered(this);
        if (visitor.visitSubtree(this)) {
            for (int i = 0, ar = arity(); i < ar; i++) {
                sub(i).execPostOrder(visitor);
            }
        }
        visitor.visit(this);
        visitor.subtreeLeft(this);
    }


    @Override
    public void execPreOrder(Visitor visitor) {
        visitor.subtreeEntered(this);
        visitor.visit(this);
        if (visitor.visitSubtree(this)) {
            for (int i = 0, ar = arity(); i < ar; i++) {
                sub(i).execPreOrder(visitor);
            }
        }
        visitor.subtreeLeft(this);
    }

    /**
     * Checks whether the Term is valid on the top level. If this is the case this method returns
     * the Term unmodified. Otherwise, a TermCreationException is thrown.
     */
    public Term checked() {
        op.validTopLevelException(this);
        return this;
        /*
         * if (op.validTopLevel(this)) { return this; } else { throw new TermCreationException(op,
         * this); }
         */
    }

    public boolean containsCodeBlockRecursive() {
        if (containsCodeBlockRecursive == ThreeValuedTruth.UNKNOWN) {
            ThreeValuedTruth result = ThreeValuedTruth.FALSE;
            if (op instanceof Modality mod && !((RustyBlock) mod.program()).isEmpty()) {
                result = ThreeValuedTruth.TRUE;
            } else {
                for (int i = 0, arity = subs.size(); i < arity; i++) {
                    var sub = (TermImpl) subs.get(i);
                    if (sub.containsCodeBlockRecursive()) {
                        result = ThreeValuedTruth.TRUE;
                        break;
                    }
                }
            }
            this.containsCodeBlockRecursive = result;
        }
        return containsCodeBlockRecursive == ThreeValuedTruth.TRUE;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (op() instanceof Modality mod) {
            if (mod.kind() == org.key_project.rusty.logic.op.Modality.RustyModalityKind.DIA) {
                sb.append("\\<").append(mod.program()).append("\\>");
            } else {
                sb.append("\\[").append(mod.program()).append("\\]");
            }
            sb.append("(").append(sub(0)).append(")");
            return sb.toString();
        } else {
            sb.append(op().name());
            if (!boundVars.isEmpty()) {
                sb.append(Strings.formatAsList(boundVars(), "{", ",", "}"));
            }
            if (arity() == 0) {
                return sb.toString();
            }
            sb.append(Strings.formatAsList(subs(), "(", ",", ")"));
            return sb.toString();
        }
    }
}
