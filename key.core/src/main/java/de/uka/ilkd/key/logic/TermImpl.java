/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.concurrent.atomic.AtomicInteger;

import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;

import org.key_project.logic.Name;
import org.key_project.logic.Property;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.Strings;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;


/**
 * The currently only class implementing the Term interface. TermFactory should be the only class
 * dealing directly with the TermImpl class.
 */
class TermImpl implements JTerm {

    /**
     * A static empty list of terms used for memory reasons.
     */
    private static final ImmutableArray<JTerm> EMPTY_TERM_LIST = new ImmutableArray<>();

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
    private final ImmutableArray<JTerm> subs;
    private final ImmutableArray<QuantifiableVariable> boundVars;

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

    private Sort sort;

    /**
     * This flag indicates that the {@link JTerm} itself or one of its children has a modality as
     * operator, that is, carries a program. A program with no statements counts as well: the
     * modality is still there, and its {@link JavaBlock} still carries meta information such as
     * {@link PositionInfo}s. Terms with this flag can't be cached because two of them may differ
     * only in that meta information.
     */
    private ThreeValuedTruth containsJavaBlockRecursive = ThreeValuedTruth.UNKNOWN;

    /** caches whether this term or a (direct/indirect) child has a {@link Transformer} operator. */
    private ThreeValuedTruth containsTransformerRecursive = ThreeValuedTruth.UNKNOWN;

    /**
     * Cached renaming-invariant hashCode ({@link RenamingTermProperty#hashCodeModThisProperty}),
     * used to fast-reject unequal pairs in equality modulo renaming. {@code 0} = not yet computed.
     */
    private int hashcodeModRenaming = 0;

    /**
     * Cached {@link #nameHash()} value. {@code 0} = not yet computed.
     */
    private int nameHash = 0;

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
     */
    public TermImpl(Operator op, ImmutableArray<JTerm> subs,
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
     * the Term unmodified. Otherwise, a TermCreationException is thrown.
     */
    public JTerm checked() {
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
    public ImmutableArray<JTerm> subs() {
        return subs;
    }


    @Override
    public JTerm sub(int nr) {
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
    public @NonNull JavaBlock javaBlock() {
        if (op instanceof JModality mod) {
            return mod.programBlock();
        } else {
            return JavaBlock.EMPTY_JAVABLOCK;
        }
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
    public int nameHash() {
        if (nameHash == 0) {
            int h = 5;
            h = h * 31 + op.name().toString().hashCode();
            h = h * 31 + arity();
            for (int i = 0, n = arity(); i < n; i++) {
                h = h * 31 + sub(i).nameHash();
            }
            if (h == 0) {
                h = 1;
            }
            nameHash = h;
        }
        return nameHash;
    }

    @Override
    public int depth() {
        if (depth == -1) {
            int localDepth = -1;
            for (int i = 0, n = arity(); i < n; i++) {
                final int subTermDepth = sub(i).depth();
                if (subTermDepth > localDepth) {
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
                && boundVars.equals(t.boundVars)
                // TODO (DD): below is no longer necessary
                && javaBlock().equals(t.javaBlock());
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

    @Override
    public <V> boolean equalsModProperty(Object o, Property<? super JTerm> property, V... v) {
        if (!(o instanceof JTerm other)) {
            return false;
        }
        return property.equalsModThisProperty(this, other);
    }

    @Override
    public int hashCodeModProperty(Property<? super JTerm> property) {
        return property.hashCodeModThisProperty(this);
    }


    /**
     * returns a linearized textual representation of this term
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (!javaBlock().isEmpty()) {
            var op = (JModality) op();
            if (op.kind() == JModality.JavaModalityKind.DIA) {
                sb.append("\\<").append(javaBlock()).append("\\> ");
            } else if (op.kind() == JModality.JavaModalityKind.BOX) {
                sb.append("\\[").append(javaBlock()).append("\\] ");
            } else {
                sb.append(op()).append("|{").append(javaBlock()).append("}| ");
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
            if (op instanceof JModality) {
                // a modality with an empty program still counts: the program is part of the
                // term, and its JavaBlock still carries position information
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

    /**
     * Renaming-invariant hashCode, computed lazily on first use and cached. Used by
     * {@link RenamingTermProperty} to fast-reject pairs that cannot be equal modulo renaming.
     */
    public int hashCodeModRenaming() {
        if (hashcodeModRenaming == 0) {
            final int h = de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY
                    .hashCodeModThisProperty(this);
            hashcodeModRenaming = h == 0 ? 1 : h;
        }
        return hashcodeModRenaming;
    }

    @Override
    public boolean containsTransformerRecursive() {
        if (containsTransformerRecursive == ThreeValuedTruth.UNKNOWN) {
            ThreeValuedTruth result = ThreeValuedTruth.FALSE;
            if (op instanceof Transformer) {
                result = ThreeValuedTruth.TRUE;
            } else {
                for (int i = 0, arity = subs.size(); i < arity; i++) {
                    if (subs.get(i).containsTransformerRecursive()) {
                        result = ThreeValuedTruth.TRUE;
                        break;
                    }
                }
            }
            this.containsTransformerRecursive = result;
        }
        return containsTransformerRecursive == ThreeValuedTruth.TRUE;
    }


}
