/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.EqualsModProofIrrelevancyUtil;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;


/**
 * The currently only class implementing the Term interface. TermFactory should be the only class
 * dealing directly with the TermImpl class.
 */
public class TermImpl implements Term, EqualsModProofIrrelevancy {

    /**
     * A static empty list of terms used for memory reasons.
     */
    private static final ImmutableArray<Term> EMPTY_TERM_LIST = new ImmutableArray<>();

    /**
     * A static empty list of quantifiable variables used for memory reasons.
     */
    private static final ImmutableArray<QuantifiableVariable> EMPTY_VAR_LIST =
        new ImmutableArray<>();

    /**
     * A static empty list of term labels used for memory reasons.
     */
    private static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST =
        new ImmutableArray<>();

    private static final AtomicInteger serialNumberCounter = new AtomicInteger();
    private final int serialNumber = serialNumberCounter.incrementAndGet();

    // content
    private final Operator op;
    private final ImmutableArray<Term> subs;
    private final ImmutableArray<QuantifiableVariable> boundVars;
    private final JavaBlock javaBlock;

    // caches
    private enum ThreeValuedTruth {
        TRUE, FALSE, UNKNOWN
    }

    private int depth = -1;
    /**
     * A cached value for computing the term's rigidness.
     */
    private ThreeValuedTruth rigid = ThreeValuedTruth.UNKNOWN;
    private ImmutableSet<QuantifiableVariable> freeVars = null;
    /**
     * Cached {@link #hashCode()} value.
     */
    private int hashcode = -1;
    /**
     * Cached {@link #hashCodeModProofIrrelevancy()} value.
     */
    private int hashcode2 = -1;

    /**
     * This flag indicates that the {@link Term} itself or one of its children contains a non empty
     * {@link JavaBlock}. {@link Term}s which provides a {@link JavaBlock} directly or indirectly
     * can't be cached because it is possible that the contained meta information inside the
     * {@link JavaBlock}, e.g. {@link PositionInfo}s, are different.
     */
    private ThreeValuedTruth containsJavaBlockRecursive = ThreeValuedTruth.UNKNOWN;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Constructs a term for the given operator, with the given sub terms, bounded variables and (if
     * applicable) the code block on this term.
     *
     * @param op the operator of the term, e.g., some arithmetic operation
     * @param subs the sub terms of the constructed term (whose type is constrained by the used
     *        operator)
     * @param boundVars the bounded variables (if applicable), e.g., for quantifiers
     * @param javaBlock the code block (if applicable) after which the term is evaluated
     */
    public TermImpl(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars, JavaBlock javaBlock) {
        assert op != null;
        assert subs != null;
        this.op = op;
        this.subs = subs.size() == 0 ? EMPTY_TERM_LIST : subs;
        this.boundVars = boundVars == null ? EMPTY_VAR_LIST : boundVars;
        this.javaBlock = javaBlock == null ? JavaBlock.EMPTY_JAVABLOCK : javaBlock;
    }



    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------


    private ImmutableSet<QuantifiableVariable> determineFreeVars() {
        ImmutableSet<QuantifiableVariable> localFreeVars =
            DefaultImmutableSet.nil();

        if (op instanceof QuantifiableVariable) {
            localFreeVars = localFreeVars.add((QuantifiableVariable) op);
        }
        for (int i = 0, ar = arity(); i < ar; i++) {
            ImmutableSet<QuantifiableVariable> subFreeVars = sub(i).freeVars();
            for (int j = 0, sz = varsBoundHere(i).size(); j < sz; j++) {
                subFreeVars = subFreeVars.remove(varsBoundHere(i).get(j));
            }
            localFreeVars = localFreeVars.union(subFreeVars);
        }
        return localFreeVars;
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Checks whether the Term is valid on the top level. If this is the case this method returns
     * the Term unmodified. Otherwise a TermCreationException is thrown.
     */
    public Term checked() {
        op.validTopLevelException(this);
        return this;
        /*
         * if (op.validTopLevel(this)) { return this; } else { throw new TermCreationException(op,
         * this); }
         */
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
    public JavaBlock javaBlock() {
        return javaBlock;
    }


    @Override
    public int arity() {
        return op.arity();
    }


    @Override
    public Sort sort() {
        return op.sort(subs);
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


    @Override
    public final boolean equalsModRenaming(Term o) {
        if (o == this) {
            return true;
        }
        return unifyHelp(this, o, ImmutableSLList.nil(),
            ImmutableSLList.nil(), null);
    }

    //
    // equals modulo renaming logic


    /**
     * compare two quantifiable variables if they are equal modulo renaming
     *
     * @param ownVar first QuantifiableVariable to be compared
     * @param cmpVar second QuantifiableVariable to be compared
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     */
    private static boolean compareBoundVariables(QuantifiableVariable ownVar,
            QuantifiableVariable cmpVar, ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars) {

        final int ownNum = indexOf(ownVar, ownBoundVars);
        final int cmpNum = indexOf(cmpVar, cmpBoundVars);

        if (ownNum == -1 && cmpNum == -1) {
            // if both variables are not bound the variables have to be the
            // same object
            return ownVar == cmpVar;
        }

        // otherwise the variables have to be bound at the same point (and both
        // be bound)
        return ownNum == cmpNum;
    }

    /**
     * @return the index of the first occurrence of <code>var</code> in <code>list</code>, or
     *         <code>-1</code> if the variable is not an element of the list
     */
    private static int indexOf(QuantifiableVariable var, ImmutableList<QuantifiableVariable> list) {
        int res = 0;
        while (!list.isEmpty()) {
            if (list.head() == var) {
                return res;
            }
            ++res;
            list = list.tail();
        }
        return -1;
    }

    /**
     * Compares two terms modulo bound renaming
     *
     * @param t0 the first term
     * @param t1 the second term
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     * @return <code>true</code> is returned iff the terms are equal modulo bound renaming
     */
    private boolean unifyHelp(Term t0, Term t1, ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars, NameAbstractionTable nat) {

        if (t0 == t1 && ownBoundVars.equals(cmpBoundVars)) {
            return true;
        }

        final Operator op0 = t0.op();

        if (op0 instanceof QuantifiableVariable) {
            return handleQuantifiableVariable(t0, t1, ownBoundVars, cmpBoundVars);
        }

        final Operator op1 = t1.op();

        if (!(op0 instanceof ProgramVariable) && op0 != op1) {
            return false;
        }

        if (t0.sort() != t1.sort() || t0.arity() != t1.arity()) {
            return false;
        }

        nat = handleJava(t0, t1, nat);
        if (nat == FAILED) {
            return false;
        }

        return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    private boolean handleQuantifiableVariable(Term t0, Term t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars) {
        return (t1.op() instanceof QuantifiableVariable)
                && compareBoundVariables((QuantifiableVariable) t0.op(),
                    (QuantifiableVariable) t1.op(), ownBoundVars, cmpBoundVars);
    }

    /**
     * used to encode that <tt>handleJava</tt> results in an unsatisfiable constraint (faster than
     * using exceptions)
     */
    private static final NameAbstractionTable FAILED = new NameAbstractionTable();

    private static NameAbstractionTable handleJava(Term t0, Term t1, NameAbstractionTable nat) {

        if (!t0.javaBlock().isEmpty() || !t1.javaBlock().isEmpty()) {
            nat = checkNat(nat);
            if (!t0.javaBlock().equalsModRenaming(t1.javaBlock(), nat)) {
                return FAILED;
            }
        }

        if (!(t0.op() instanceof SchemaVariable) && t0.op() instanceof ProgramVariable) {
            if (!(t1.op() instanceof ProgramVariable)) {
                return FAILED;
            }
            nat = checkNat(nat);
            if (!((ProgramVariable) t0.op()).equalsModRenaming((ProgramVariable) t1.op(), nat)) {
                return FAILED;
            }
        }

        return nat;
    }

    private boolean descendRecursively(Term t0, Term t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars, NameAbstractionTable nat) {

        for (int i = 0; i < t0.arity(); i++) {
            ImmutableList<QuantifiableVariable> subOwnBoundVars = ownBoundVars;
            ImmutableList<QuantifiableVariable> subCmpBoundVars = cmpBoundVars;

            if (t0.varsBoundHere(i).size() != t1.varsBoundHere(i).size()) {
                return false;
            }
            for (int j = 0; j < t0.varsBoundHere(i).size(); j++) {
                final QuantifiableVariable ownVar = t0.varsBoundHere(i).get(j);
                final QuantifiableVariable cmpVar = t1.varsBoundHere(i).get(j);
                if (ownVar.sort() != cmpVar.sort()) {
                    return false;
                }

                subOwnBoundVars = subOwnBoundVars.prepend(ownVar);
                subCmpBoundVars = subCmpBoundVars.prepend(cmpVar);
            }

            boolean newConstraint =
                unifyHelp(t0.sub(i), t1.sub(i), subOwnBoundVars, subCmpBoundVars, nat);

            if (!newConstraint) {
                return false;
            }
        }

        return true;
    }

    private static NameAbstractionTable checkNat(NameAbstractionTable nat) {
        if (nat == null) {
            return new NameAbstractionTable();
        }
        return nat;
    }

    // end of equals modulo renaming logic


    /**
     * true iff <code>o</code> is syntactically equal to this term
     */
    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }

        if (o == null || o.getClass() != getClass() || hashCode() != o.hashCode()) {
            return false;
        }

        final TermImpl t = (TermImpl) o;

        return op.equals(t.op) && t.hasLabels() == hasLabels() && subs.equals(t.subs)
                && boundVars.equals(t.boundVars) && javaBlock.equals(t.javaBlock);
    }

    @Override
    public boolean equalsModIrrelevantTermLabels(Object o) {
        if (o == this) {
            return true;
        }

        if (!(o instanceof TermImpl)) {
            return false;
        }

        final TermImpl t = (TermImpl) o;

        if (!(op.equals(t.op) && boundVars.equals(t.boundVars) && javaBlock.equals(t.javaBlock))) {
            return false;
        }

        Term other = (Term) o;

        for (TermLabel label : getLabels()) {
            if (label.isProofRelevant() && !other.getLabels().contains(label)) {
                return false;
            }
        }

        for (TermLabel label : other.getLabels()) {
            if (label.isProofRelevant() && !getLabels().contains(label)) {
                return false;
            }
        }

        for (int i = 0; i < subs.size(); ++i) {
            if (!subs.get(i).equalsModIrrelevantTermLabels(t.subs.get(i))) {
                return false;
            }
        }

        return true;
    }

    @Override
    public boolean equalsModTermLabels(Object o) {
        if (o == this) {
            return true;
        }

        if (!(o instanceof TermImpl)) {
            return false;
        }

        final TermImpl t = (TermImpl) o;

        if (!(op.equals(t.op) && boundVars.equals(t.boundVars) && javaBlock.equals(t.javaBlock))) {
            return false;
        }

        for (int i = 0; i < subs.size(); ++i) {
            if (!subs.get(i).equalsModTermLabels(t.subs.get(i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean equalsModProofIrrelevancy(Object o) {
        if (o == this) {
            return true;
        }

        if (!(o instanceof TermImpl)) {
            return false;
        }

        final TermImpl t = (TermImpl) o;

        boolean opResult = op.equalsModProofIrrelevancy(t.op);
        if (!(opResult
                && EqualsModProofIrrelevancyUtil.compareImmutableArrays(boundVars, t.boundVars)
                && javaBlock.equalsModProofIrrelevancy(t.javaBlock))) {
            return false;
        }

        Term other = (Term) o;

        for (TermLabel label : getLabels()) {
            if (label.isProofRelevant() && !other.getLabels().contains(label)) {
                return false;
            }
        }

        for (TermLabel label : other.getLabels()) {
            if (label.isProofRelevant() && !getLabels().contains(label)) {
                return false;
            }
        }

        for (int i = 0; i < subs.size(); ++i) {
            if (!subs.get(i).equalsModProofIrrelevancy(t.subs.get(i))) {
                return false;
            }
        }

        return true;
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        if (hashcode2 == -1) {
            // compute into local variable first to be thread-safe.
            this.hashcode2 = Objects.hash(op(),
                EqualsModProofIrrelevancyUtil
                        .hashCodeIterable(subs()),
                EqualsModProofIrrelevancyUtil.hashCodeIterable(boundVars()), javaBlock());
            if (hashcode2 == -1) {
                hashcode2 = 0;
            }
        }
        return hashcode2;
    }

    @Override
    public final int hashCode() {
        if (hashcode == -1) {
            // compute into local variable first to be thread-safe.
            this.hashcode = computeHashCode();
        }
        return hashcode;
    }


    /**
     * Performs the actual computation of the hashcode and can be overwritten by subclasses if
     * necessary
     */
    protected int computeHashCode() {
        int hashcode = 5;
        hashcode = hashcode * 17 + op().hashCode();
        hashcode = hashcode * 17 + subs().hashCode();
        hashcode = hashcode * 17 + boundVars().hashCode();
        hashcode = hashcode * 17 + javaBlock().hashCode();

        if (hashcode == -1) {
            hashcode = 0;
        }
        return hashcode;
    }


    /**
     * returns a linearized textual representation of this term
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (!javaBlock.isEmpty()) {
            if (op() == Modality.DIA) {
                sb.append("\\<").append(javaBlock).append("\\> ");
            } else if (op() == Modality.BOX) {
                sb.append("\\[").append(javaBlock).append("\\] ");
            } else {
                sb.append(op()).append("\\[").append(javaBlock).append("\\] ");
            }
            sb.append("(").append(sub(0)).append(")");
            return sb.toString();
        } else {
            sb.append(op().name().toString());
            if (!boundVars.isEmpty()) {
                sb.append("{");
                for (int i = 0, n = boundVars.size(); i < n; i++) {
                    sb.append(boundVars.get(i));
                    if (i < n - 1) {
                        sb.append(", ");
                    }
                }
                sb.append("}");
            }
            if (arity() == 0) {
                return sb.toString();
            }
            sb.append("(");
            for (int i = 0, ar = arity(); i < ar; i++) {
                sb.append(sub(i));
                if (i < ar - 1) {
                    sb.append(",");
                }
            }
            sb.append(")");
        }

        return sb.toString();
    }


    @Override
    public int serialNumber() {
        return serialNumber;
    }

    @Override
    public boolean hasLabels() {
        return false;
    }

    @Override
    public boolean containsLabel(TermLabel label) {
        return false;
    }

    @Override
    public TermLabel getLabel(Name termLabelName) {
        return null;
    }

    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return EMPTY_LABEL_LIST;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean containsJavaBlockRecursive() {
        if (containsJavaBlockRecursive == ThreeValuedTruth.UNKNOWN) {
            ThreeValuedTruth result = ThreeValuedTruth.FALSE;
            if (javaBlock != null && !javaBlock.isEmpty()) {
                result = ThreeValuedTruth.TRUE;
            } else {
                for (int i = 0, arity = subs.size(); i < arity; i++) {
                    if (subs.get(i).containsJavaBlockRecursive()) {
                        result = ThreeValuedTruth.TRUE;
                        break;
                    }
                }
            }
            this.containsJavaBlockRecursive = result;
        }
        return containsJavaBlockRecursive == ThreeValuedTruth.TRUE;
    }

    private String origin;

    @Override
    public @Nullable String getOrigin() {
        return origin;
    }

    public void setOrigin(String origin) {
        this.origin = origin;
    }
}
