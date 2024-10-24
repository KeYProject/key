/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.rusty.Services;
import org.key_project.rusty.ldt.IntLDT;
import org.key_project.rusty.logic.op.*;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class TermBuilder {
    private final TermFactory tf;
    private final Term tt;
    private final Term ff;
    private final Services services;

    public TermBuilder(TermFactory tf, Services services) {
        this.tf = tf;
        this.tt = tf.createTerm(Junctor.TRUE);
        this.ff = tf.createTerm(Junctor.FALSE);
        this.services = services;
    }

    public TermFactory tf() {
        return tf;
    }

    // -------------------------------------------------------------------------
    // constructors for special classes of term operators
    // -------------------------------------------------------------------------

    public Term var(LogicVariable v) {
        return tf.createTerm(v);
    }

    public Term var(BoundVariable v) {
        return tf.createTerm(v);
    }

    public Term var(ProgramVariable v) {
        return tf.createTerm(v);
    }

    public ImmutableList<Term> var(ProgramVariable... vs) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (ProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }

    public ImmutableList<Term> var(Iterable<? extends ProgramVariable> vs) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (ProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }

    public Term tt() {
        return tt;
    }

    public Term ff() {
        return ff;
    }

    public Term all(QuantifiableVariable qv, Term t) {
        return tf.createTerm(Quantifier.ALL, new ImmutableArray<>(t),
            new ImmutableArray<>(qv));
    }

    public Term all(Iterable<? extends QuantifiableVariable> qvs, Term t) {
        Term result = t;
        for (QuantifiableVariable fv : qvs) {
            result = all(fv, result);
        }
        return result;
    }

    public Term allClose(Term t) {
        return all(t.freeVars(), t);
    }

    public Term ex(QuantifiableVariable qv, Term t) {
        return tf.createTerm(Quantifier.EX, new ImmutableArray<>(t),
            new ImmutableArray<>(qv));
    }

    public Term ex(Iterable<? extends QuantifiableVariable> qvs, Term t) {
        Term result = t;
        for (QuantifiableVariable fv : qvs) {
            result = ex(fv, result);
        }
        return result;
    }

    public Term not(Term t) {
        if (t.op() == Junctor.TRUE) {
            return ff();
        } else if (t.op() == Junctor.FALSE) {
            return tt();
        } else if (t.op() == Junctor.NOT) {
            return t.sub(0);
        } else {
            return tf.createTerm(Junctor.NOT, t);
        }
    }

    public Term and(Term t1, Term t2) {
        if (t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE) {
            return ff();
        } else if (t1.op() == Junctor.TRUE) {
            return t2;
        } else if (t2.op() == Junctor.TRUE) {
            return t1;
        } else {
            return tf.createTerm(Junctor.AND, t1, t2);
        }
    }

    public Term and(Term... subTerms) {
        Term result = tt();
        for (Term sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    public Term and(Iterable<? extends Term> subTerms) {
        Term result = tt();
        for (Term sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    public Term or(Term t1, Term t2) {
        if (t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE) {
            return tt();
        } else if (t1.op() == Junctor.FALSE) {
            return t2;
        } else if (t2.op() == Junctor.FALSE) {
            return t1;
        } else {
            return tf.createTerm(Junctor.OR, t1, t2);
        }
    }

    public Term or(Term... subTerms) {
        Term result = ff();
        for (Term sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    public Term or(Iterable<? extends Term> subTerms) {
        Term result = ff();
        for (Term sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    public Term imp(Term t1, Term t2) {
        if (t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return tt();
        } else if (t1.op() == Junctor.TRUE) {
            return t2;
        } else if (t2.op() == Junctor.FALSE) {
            return not(t1);
        } else {
            return tf.createTerm(Junctor.IMP, t1, t2);
        }
    }

    /**
     * Creates a term with the correct equality symbol for the sorts involved
     */
    public Term equals(Term t1, Term t2) {
        if (t1.sort() == RustyDLTheory.FORMULA) {
            if (t1.op() == Junctor.TRUE) {
                return t2;
            } else if (t2.op() == Junctor.TRUE) {
                return t1;
            } else if (t1.op() == Junctor.FALSE) {
                return not(t2);
            } else if (t2.op() == Junctor.FALSE) {
                return not(t1);
            } else {
                return tf.createTerm(Equality.EQV, t1, t2);
            }
        } else {
            return tf.createTerm(Equality.EQUALS, t1, t2);
        }
    }

    public Term func(Function f) {
        return tf.createTerm(f);
    }

    public Term func(Function f, Term... subs) {
        return tf.createTerm(f, subs);
    }

    public Term func(Function f, Term s) {
        return tf.createTerm(f, s);
    }

    public Term func(Function f, Term[] s, ImmutableArray<QuantifiableVariable> boundVars) {
        return tf.createTerm(f, s, boundVars);
    }

    public Term prog(Modality.RustyModalityKind modKind, RustyBlock jb, Term t) {
        return tf.createTerm(Modality.getModality(modKind, jb), new Term[] { t }, null);
    }

    public Term box(RustyBlock jb, Term t) {
        return prog(Modality.RustyModalityKind.BOX, jb, t);
    }

    public Term dia(RustyBlock jb, Term t) {
        return prog(Modality.RustyModalityKind.DIA, jb, t);
    }

    public Term ife(Term cond, Term _then, Term _else) {
        return tf.createTerm(IfThenElse.IF_THEN_ELSE, cond, _then, _else);
    }

    // -------------------------------------------------------------------------
    // updates
    // -------------------------------------------------------------------------

    public Term elementary(UpdateableOperator lhs, Term rhs) {
        ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);
        return tf.createTerm(eu, rhs);
    }

    public Term elementary(Term lhs, Term rhs) {
        if (lhs.op() instanceof UpdateableOperator) {
            assert lhs.arity() == 0 : "uh oh: " + lhs;
            return elementary((UpdateableOperator) lhs.op(), rhs);
        } else if (lhs.op() == UpdateApplication.UPDATE_APPLICATION) {
            // #1536 A nested updates like
            // { {a:=1} b :=a}
            // should be parsed as (see KeY-Book, Sec. 3.4.1, Def. 3.8)
            // { {a:=1} (b :=a)}
            // but is parsed as:
            // { ({a:=1} b) :=a}
            // The latter is (currently) not supported, hence the exception.
            throw new TermCreationException("lhs cannot have a nested update. "
                + "If you have a nested update like '{{a:=1} b:=a}', "
                + "replace it with the bracketed version '{{a:=1} (b:=a)}'.");
        } else {
            throw new TermCreationException("Not a legal lhs: " + lhs);
        }
    }

    public Term skip() {
        return tf.createTerm(UpdateJunctor.SKIP);
    }

    public Term parallel(Term u1, Term u2) {
        if (u1.sort() != RustyDLTheory.UPDATE) {
            throw new TermCreationException("Not an update: " + u1);
        } else if (u2.sort() != RustyDLTheory.UPDATE) {
            throw new TermCreationException("Not an update: " + u2);
        }
        if (u1.op() == UpdateJunctor.SKIP) {
            return u2;
        } else if (u2.op() == UpdateJunctor.SKIP) {
            return u1;
        }
        return tf.createTerm(UpdateJunctor.PARALLEL_UPDATE, u1, u2);
    }

    public Term parallel(Term... updates) {
        Term result = skip();
        for (Term update : updates) {
            result = parallel(result, update);
        }
        return result;
    }

    public Term parallel(ImmutableList<Term> updates) {
        return parallel(updates.toArray(new Term[updates.size()]));
    }

    public Term parallel(Term[] lhss, Term[] values) {
        if (lhss.length != values.length) {
            throw new TermCreationException("Tried to create parallel update with " + lhss.length
                + " locs and " + values.length + " values");
        }
        Term[] updates = new Term[lhss.length];
        for (int i = 0; i < updates.length; i++) {
            updates[i] = elementary(lhss[i], values[i]);
        }
        return parallel(updates);
    }

    public Term parallel(Iterable<Term> lhss, Iterable<Term> values) {
        ImmutableList<Term> updates = ImmutableSLList.nil();
        Iterator<Term> lhssIt = lhss.iterator();
        Iterator<Term> rhssIt = values.iterator();
        while (lhssIt.hasNext()) {
            assert rhssIt.hasNext();
            updates = updates.append(elementary(lhssIt.next(), rhssIt.next()));
        }
        return parallel(updates);
    }

    public Term sequential(Term u1, Term u2) {
        return parallel(u1, apply(u1, u2));
    }

    public Term sequential(ImmutableList<Term> updates) {
        if (updates.isEmpty()) {
            return skip();
        } else if (updates.size() == 1) {
            return updates.head();
        } else {
            return sequential(updates.head(), sequential(updates.tail()));
        }
    }

    public ImmutableList<Term> apply(Term update, ImmutableList<Term> targets) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (Term target : targets) {
            result = result.append(apply(update, target));
        }
        return result;
    }

    public Term apply(Term update, Term target) {
        if (update.sort() != RustyDLTheory.UPDATE) {
            throw new TermCreationException("Not an update: " + update);
        } else if (update.op() == UpdateJunctor.SKIP) {
            return target;
        } else if (target.equals(tt())) {
            return tt();
        } else {
            return tf.createTerm(UpdateApplication.UPDATE_APPLICATION, update, target);
        }
    }

    public Term applyParallel(ImmutableList<Term> updates, Term target) {
        return apply(parallel(updates), target);
    }

    public Term applyParallel(Term[] lhss, Term[] values, Term target) {
        return apply(parallel(lhss, values), target);
    }

    public Term applySequential(Term[] updates, Term target) {
        if (updates.length == 0) {
            return target;
        } else {
            ImmutableList<Term> updateList = ImmutableSLList.<Term>nil().append(updates).tail();
            return apply(updates[0], applySequential(updateList, target));
        }
    }

    public Term applySequential(ImmutableList<Term> updates, Term target) {
        if (updates.isEmpty()) {
            return target;
        } else {
            return apply(updates.head(), applySequential(updates.tail(), target));
        }
    }

    // -------------------------------------------------------------------------
    // boolean operators
    // -------------------------------------------------------------------------

    public Term TRUE() {
        return services.getLDTs().getBoolLDT().getTrueTerm();
    }

    public Term FALSE() {
        return services.getLDTs().getBoolLDT().getFalseTerm();
    }

    // -------------------------------------------------------------------------
    // integer operators
    // -------------------------------------------------------------------------

    public Term geq(Term t1, Term t2) {
        final IntLDT integerLDT = services.getLDTs().getIntLDT();
        return func(integerLDT.getGreaterOrEquals(), t1, t2);
    }

    public Term gt(Term t1, Term t2) {
        final IntLDT integerLDT = services.getLDTs().getIntLDT();
        return func(integerLDT.getGreaterThan(), t1, t2);
    }

    public Term lt(Term t1, Term t2) {
        final IntLDT integerLDT = services.getLDTs().getIntLDT();
        return func(integerLDT.getLessThan(), t1, t2);
    }

    public Term leq(Term t1, Term t2) {
        final IntLDT integerLDT = services.getLDTs().getIntLDT();
        return func(integerLDT.getLessOrEquals(), t1, t2);
    }

    public Term zero() {
        return services.getLDTs().getIntLDT().zero();
    }

    public Term one() {
        return services.getLDTs().getIntLDT().one();
    }

    /**
     * Creates terms to be used in Z/C/FP/DFP/R notations. The result does not have such a
     * constructor applied yet.
     *
     * @param numberString a string containing the number in a decimal representation
     * @return Term in "number" notation representing the given number
     * @throws NumberFormatException if <code>numberString</code> is not a number
     */
    private Term numberTerm(String numberString) {
        if (numberString == null || numberString.isEmpty()) {
            throw new NumberFormatException(numberString + " is not a number.");
        }

        Term numberLiteralTerm;
        boolean negate = false;
        int j = 0;

        final IntLDT intLDT = services.getLDTs().getIntLDT();

        if (numberString.charAt(0) == '-') {
            negate = true;
            j = 1;
        }
        numberLiteralTerm = func(intLDT.getNumberTerminator());

        int digit;
        for (int i = j, sz = numberString.length(); i < sz; i++) {
            char c = numberString.charAt(i);
            if ('0' <= c && c <= '9') {
                digit = c - '0';
            } else {
                throw new NumberFormatException(numberString + " is not a number.");
            }
            numberLiteralTerm = func(intLDT.getNumberLiteralFor(digit), numberLiteralTerm);
        }
        if (negate) {
            numberLiteralTerm = func(intLDT.getNegativeNumberSign(), numberLiteralTerm);
        }

        // return the raw number literal term ('C', 'Z' or 'R' must still be added)
        return numberLiteralTerm;
    }

    /**
     * Get term for an integer literal.
     *
     * @param numberString String representing an integer with radix 10, may be negative
     * @return Term in Z-Notation representing the given number
     * @throws NumberFormatException if <code>numberString</code> is not a number
     */
    public Term zTerm(String numberString) {
        return func(services.getLDTs().getIntLDT().getNumberSymbol(),
            numberTerm(numberString));
    }

    /**
     * Get term for an integer literal.
     *
     * @param number an integer
     * @return Term in Z-Notation representing the given number
     */
    public Term zTerm(long number) {
        return zTerm(Long.toString(number));
    }

    public Term add(Term t1, Term t2) {
        final IntLDT integerLDT = services.getLDTs().getIntLDT();
        final Term zero = integerLDT.zero();
        if (t1.equals(zero)) {
            return t2;
        } else if (t2.equals(zero)) {
            return t1;
        } else {
            return func(integerLDT.getAdd(), t1, t2);
        }
    }

    public Term applyUpdatePairsSequential(ImmutableList<Term> updates, Term target) {
        if (updates.isEmpty()) {
            return target;
        } else {
            return apply(updates.head(),
                applyUpdatePairsSequential(updates.tail(), target));
        }
    }

    /**
     * Creates a substitution term
     *
     * @param substVar the QuantifiableVariable to be substituted
     * @param substTerm the Term that replaces substVar
     * @param origTerm the Term that is substituted
     */
    public Term subst(SubstOp op, QuantifiableVariable substVar, Term substTerm, Term origTerm) {
        return tf.createTerm(op, new ImmutableArray<>(substTerm, origTerm),
            new ImmutableArray<>(substVar));
    }

    public Term mutRef(MutRef mRef) {
        return tf.createTerm(mRef);
    }
}
