/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.pp;

import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.logic.op.*;
import org.key_project.rusty.logic.op.sv.*;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * Encapsulate the concrete syntax used to print a term. The {@link NotationInfo} class associates a
 * Notation with every {@link Operator}. The various inner classes of this
 * class represent different kinds of concrete syntax, like prefix, infix, postfix, function style,
 * attribute style, etc.
 */
public abstract class Notation {
    /**
     * The priority of this operator in the given concrete syntax. This is used to determine whether
     * parentheses are required around a subterm.
     */
    private final int priority;

    /** Create a Notation with a given priority. */
    protected Notation(int priority) {
        this.priority = priority;
    }

    /** get the priority of the term */
    public final int getPriority() {
        return priority;
    }

    /**
     * Print a term to a {@link LogicPrinter}. Concrete subclasses override this to call one of the
     * <code>printXYZTerm</code> of {@link LogicPrinter}, which do the layout.
     */
    public abstract void print(Term t, LogicPrinter sp);

    /**
     * Print a term without beginning a new block. See
     * {@link LogicPrinter#printTermContinuingBlock(Term)}for the idea behind this. The standard
     * implementation just delegates to {@link #print(Term,LogicPrinter)}
     */
    public void printContinuingBlock(Term t, LogicPrinter sp) {
        print(t, sp);
    }

    /**
     * The standard concrete syntax for constants like true and false.
     */
    public static final class Constant extends Notation {
        private final String name;

        public Constant(String name, int prio) {
            super(prio);
            this.name = name;
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printConstant(t, name);
        }
    }

    /**
     * The standard concrete syntax for prefix operators.
     */
    public static final class Prefix extends Notation {
        private final String name;
        private final int ass;

        public Prefix(String name, int prio, int ass) {
            super(prio);
            this.name = name;
            this.ass = ass;
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printPrefixTerm(name, t, t.sub(0), ass);
        }

    }

    /**
     * The standard concrete syntax for infix operators.
     */
    public static final class Infix extends Notation {
        private final String name;
        private final int assLeft, assRight;

        public Infix(String name, int prio, int assLeft, int assRight) {
            super(prio);
            this.name = name;
            this.assLeft = assLeft;
            this.assRight = assRight;
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printInfixTerm(t.sub(0), assLeft, name, t, t.sub(1), assRight);
        }

        /**
         * Print a term without beginning a new block. This calls the
         * {@link LogicPrinter#printTermContinuingBlock(Term)} method.
         */
        public void printContinuingBlock(Term t, LogicPrinter sp) {
            sp.printInfixTermContinuingBlock(t.sub(0), assLeft, name, t, t.sub(1), assRight);
        }

    }

    /**
     * The standard concrete syntax for quantifiers.
     */
    public static final class Quantifier extends Notation {
        private final String name;
        private final int ass;

        public Quantifier(String name, int prio, int ass) {
            super(prio);
            this.name = name;
            this.ass = ass;
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printQuantifierTerm(name, (ImmutableArray<QuantifiableVariable>) t.varsBoundHere(0),
                t.sub(0), ass);
        }

    }


    /**
     * The standard concrete syntax for DL modalities box and diamond.
     */
    public static final class ModalityNotation extends Notation {
        private final String left, right;

        private final int ass;

        public ModalityNotation(String left, String right, int prio, int ass) {
            super(prio);
            this.left = left;
            this.right = right;
            this.ass = ass;
        }

        public void print(Term t, LogicPrinter sp) {
            assert t.op() instanceof Modality;
            var mod = (Modality) t.op();
            assert mod.program() != null;
            sp.printModalityTerm(left, mod.program(), right, t, ass);
        }
    }

    /**
     * The concrete syntax for DL modalities represented with a SchemaVariable.
     */
    public static final class ModalSVNotation extends Notation {
        private final int ass;

        public ModalSVNotation(int prio, int ass) {
            super(prio);
            this.ass = ass;
        }

        public void print(Term t, LogicPrinter sp) {
            var mod = (Modality) t.op();
            sp.printModalityTerm("\\modality{" + t.op().name() + "}", mod.program(),
                "\\endmodality", t, ass);
        }
    }

    /**
     * The standard concrete syntax for update application.
     */
    public static final class UpdateApplicationNotation extends Notation {
        public UpdateApplicationNotation() {
            super(115);
        }

        public void print(Term t, LogicPrinter sp) {
            assert t.op() == UpdateApplication.UPDATE_APPLICATION;
            final Operator targetOp = UpdateApplication.getTarget(t).op();
            final int assTarget =
                (t.sort() == RustyDLTheory.FORMULA ? (targetOp.arity() == 1 ? 60 : 85) : 110);

            sp.printUpdateApplicationTerm("{", "}", t, assTarget);
        }
    }

    /**
     * The standard concrete syntax for elementary updates.
     */
    public static final class ElementaryUpdateNotation extends Notation {
        public ElementaryUpdateNotation() {
            super(150);
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printElementaryUpdate(":=", t, 0);
        }
    }


    /**
     * The standard concrete syntax for parallel updates
     */
    public static final class ParallelUpdateNotation extends Notation {
        public ParallelUpdateNotation() {
            super(100);
        }

        public void print(Term t, LogicPrinter sp) {
            assert t.op() == UpdateJunctor.PARALLEL_UPDATE;

            sp.printParallelUpdate("||", t, 10);
        }
    }


    /**
     * The standard concrete syntax for substitution terms.
     */
    public static final class Subst extends Notation {
        public Subst() {
            super(120);
        }

        public void print(Term t, LogicPrinter sp) {
            QuantifiableVariable v = instQV(t, sp, 1);
            final int assTarget =
                (t.sort() == RustyDLTheory.FORMULA ? (t.sub(1).op() == Equality.EQUALS ? 75 : 60)
                        : 110);
            sp.printSubstTerm("{\\subst ", v, t.sub(0), 0, "}", t.sub(1), assTarget);
        }

        private QuantifiableVariable instQV(Term t, LogicPrinter sp, int subTerm) {
            QuantifiableVariable v = t.varsBoundHere(subTerm).get(0);

            if (v instanceof SchemaVariable sv) {
                Object object = sp.getInstantiations().getInstantiation(sv);
                if (object != null) {
                    v = (QuantifiableVariable) (((Term) object).op());
                }
            }
            return v;
        }
    }


    /**
     * The standard concrete syntax for function and predicate terms.
     */
    public static final class FunctionNotation extends Notation {
        public FunctionNotation() {
            super(130);
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printFunctionTerm(t);
        }
    }

    /**
     * The standard concrete syntax for conditional terms <code>if (phi) (t1) (t2)</code>.
     */
    public static final class IfThenElse extends Notation {
        private final String keyword;

        public IfThenElse(int priority, String keyw) {
            super(priority);
            keyword = keyw;
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printIfThenElseTerm(t, keyword);
        }
    }

    /**
     * The standard concrete syntax for all kinds of variables.
     */
    public static class VariableNotation extends Notation {
        public VariableNotation() {
            super(1000);
        }

        public void print(Term t, LogicPrinter sp) {
            if (t.op() instanceof ProgramVariable) {
                sp.printConstant(t.op().name().toString());
            } else if (t.op() instanceof LogicVariable) {
                sp.printConstant(t.op().name().toString());
            } else {
                sp.printConstant(t.op().name().toString());
            }
        }
    }

    public static final class SchemaVariableNotation extends VariableNotation {
        public void printDeclaration(org.key_project.logic.op.sv.SchemaVariable v,
                LogicPrinter sp) {
            String svType;String specificSort="";if(v instanceof OperatorSV){switch(v){case ProgramSV psv->{svType="\\program";specificSort=psv.sort().declarationString();}case TermSV tsv->{svType="\\term";specificSort=tsv.sort().name().toString();}case FormulaSV fsv->{svType="\\formula";specificSort=fsv.sort().name().toString();}case VariableSV varSV->{svType="\\variables";specificSort=varSV.sort().name().toString();}case UpdateSV ignored->svType="\\update";case SkolemTermSV skolemTermSV->{if(skolemTermSV.sort()==RustyDLTheory.FORMULA){svType="\\skolemFormula";}else{svType="\\skolemTerm";specificSort=skolemTermSV.sort().name().toString();}}default->throw new RuntimeException("Unknown variable type: "+v.getClass());}sp.layouter().print("\\schemaVar ").print(svType+" ").print(specificSort).print(" ").print(v.name().toString());}else if(v instanceof ModalOperatorSV modalOperatorSV){sp.layouter().beginC(0).beginC().print("\\schemaVar \\modalOperator {").brk(0);boolean first=true;for(Modality.RustyModalityKind modality:modalOperatorSV.getModalities()){if(!first){sp.layouter().print(",").brk();}else{first=false;}sp.layouter().print(modality.name().toString());}sp.layouter().end().brk(0).print("}").end().print(" ").print(modalOperatorSV.name().toString());}else{throw new RuntimeException("Unknown variable type: "+v.getClass());}
        }

        @SuppressWarnings("unchecked")
        public void print(Term t, LogicPrinter sp) {
            // logger.debug("SSV: " + t+ " [" + t.op() + "]");
            Object o = sp.getInstantiations()
                    .getInstantiation((org.key_project.logic.op.sv.SchemaVariable) (t.op()));
            if (o == null) {
                // logger.debug("Instantiation of " + t+ " [" + t.op() + "]" + "
                // not known.");
                sp.printConstant(t.op().name().toString());
            } else {
                if (o instanceof RustyProgramElement pe) {
                    // logger.debug(t.toString() + " [" + t.op() + "]" + "
                    // is a ProgramElement.");
                    sp.printProgramElement(pe);
                } else {
                    // logger.debug("Instantiation of " + t+ " [" + t.op() +
                    // "]" + " known.");
                    if (o instanceof ImmutableList) {
                        final Iterator<Object> it = ((ImmutableList<Object>) o).iterator();
                        sp.layouter().print("{");
                        while (it.hasNext()) {
                            final Object next = it.next();
                            if (next instanceof Term) {
                                sp.printTerm((Term) o);
                            } else {
                                sp.printConstant(o.toString());
                            }
                            if (it.hasNext()) {
                                sp.layouter.print(",");
                            }
                        }
                        sp.layouter().print("}");
                    } else {
                        sp.printTerm((Term) o);
                    }
                }
            }
        }
    }
}
