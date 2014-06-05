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

package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;

/**
 * The Class {@link ParameterlessTermLabel} can be used to define labels without parameters.
 *
 * You can use a {@link SingletonLabelFactory} to create a factory for an
 * instance of this class.
 *
 * @see SingletonLabelFactory
 *
 * @author mattias ulbrich
 */
public final class ParameterlessTermLabel implements TermLabel {
   /**
    * Name of {@link #ANON_HEAP_LABEL}.
    */
   public static final Name ANON_HEAP_LABEL_NAME = new Name("anonHeapFunction");

   /**
    * Label attached to anonymisation heap function symbols as for instance
    * introduce in UseOperationContractRule or WhileInvariantRule.
    */
   public static final TermLabel ANON_HEAP_LABEL =
           new ParameterlessTermLabel(ANON_HEAP_LABEL_NAME);

   /**
    * Name of {@link #SELECT_SKOLEM_LABEL}.
    */
   public static final Name SELECT_SKOLEM_LABEL_NAME = new Name("selectSK");

   /**
    * Label attached to skolem constants introduced by the rule pullOutSelect.
    */
   public static final TermLabel SELECT_SKOLEM_LABEL =
           new ParameterlessTermLabel(SELECT_SKOLEM_LABEL_NAME);

   /**
    * Name of {@link #LOOP_BODY_LABEL}.
    */
   public static final Name LOOP_BODY_LABEL_NAME = new Name("LoopBody");

   /**
    * Label attached to the modality which executes a loop body in branch
    * "Body Preserves Invariant" of applied "Loop Invariant" rules.
    */
   public static final TermLabel LOOP_BODY_LABEL =
           new ParameterlessTermLabel(LOOP_BODY_LABEL_NAME);

   /**
    * Name of {@link #LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL}.
    */
   public static final Name LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME =
           new Name("LoopInvariantNormalBehavior");

   /**
    * Label attached to the implication when a loop body execution terminated
    * normally without any exceptions, returns or breaks in branch
    * "Body Preserves Invariant" of applied "Loop Invariant" rules to show the
    * loop invariant.
    */
   public static final TermLabel LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL =
           new ParameterlessTermLabel(LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME);

   /**
    * Name of {@link #IMPLICIT_SPECIFICATION_LABEL}.
    */
   public static final Name IMPLICIT_SPECIFICATION_LABEL_NAME = new Name("impl");

   /**
    * Label attached to a term which is specified implicitly (by the JML specification).
    */
   public static final TermLabel IMPLICIT_SPECIFICATION_LABEL =
           new ParameterlessTermLabel(IMPLICIT_SPECIFICATION_LABEL_NAME);

   /**
    * Name of {@link #SHORTCUT_EVALUATION_LABEL}.
    */
   public static final Name SHORTCUT_EVALUATION_LABEL_NAME = new Name("SC");

   /**
    * Label attached to a term with the logical operator '||' or '&&' to distinguish
    * from '|' or '&' respectively.
    */
   public static final TermLabel SHORTCUT_EVALUATION_LABEL =
           new ParameterlessTermLabel(SHORTCUT_EVALUATION_LABEL_NAME);

   /**
    * Name of {@link #UNDEFINED_VALUE_LABEL}.
    */
   public static final Name UNDEFINED_VALUE_LABEL_NAME = new Name("undef");

   /**
    * Label attached to a term which denotes an undefined value. At present it is only
    * used for the else-part of the {@link #IfExThenElse} operator, when it is used
    * for the translation of JML's \min and \max operator. It is necessary to evaluate
    * this constant expression to be not well-defined.
    */
   public static final TermLabel UNDEFINED_VALUE_LABEL =
           new ParameterlessTermLabel(UNDEFINED_VALUE_LABEL_NAME);

   /**
    * Name of {@link #RESULT_LABEL}.
    */
   public static final Name RESULT_LABEL_NAME = new Name("RES");

   /**
    * Label attached to a {@link Term} to evaluate in a side proof.
    */
   public static final TermLabel RESULT_LABEL =
           new ParameterlessTermLabel(RESULT_LABEL_NAME);

    /**
     * The unique name of this label.
     * This is the basename and does not include the parameters
     */
    private final Name name;

    /**
     * Instantiates a new simple term label.
     *
     * @param name
     *            the name, not <code>null</code>
     * @param instantiator
     *            the fixed associated instantiator, may be <code>null</code>.
     */
    public ParameterlessTermLabel(Name name) {
        assert name != null;
        this.name = name;
    }

    @Override
    public Name name() {
        return name;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * Simple term labels have no parameters. This always throws an
     * {@link IndexOutOfBoundsException}.
     */
    @Override
    public Object getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * Simple term labels have no parameters. This always returns 0.
     */
    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public String toString() {
        return name.toString();
    }

    /**
     * {@inheritDoc}
     *
     * <p>This object is equal to another {@link ParameterlessTermLabel} iff they
     * bear the same name.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ParameterlessTermLabel) {
            ParameterlessTermLabel other = (ParameterlessTermLabel) obj;
            return name.equals(other.name);
        }
        else {
           return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return name.hashCode();
    }
}