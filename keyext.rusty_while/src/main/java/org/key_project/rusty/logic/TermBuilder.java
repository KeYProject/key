/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.Equality;
import org.key_project.rusty.logic.op.Junctor;
import org.key_project.rusty.logic.op.Quantifier;
import org.key_project.util.collection.ImmutableArray;

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

    public Term func(Function f, Term... subs) {
        return tf.createTerm(f, subs);
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
}
