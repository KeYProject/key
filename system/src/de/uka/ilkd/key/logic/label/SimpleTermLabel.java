// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;

/**
 * The Class SimpleTermLabel can be used to define labels without parameters.
 * 
 * You can use a {@link SingletonLabelFactory} to create a factory for an
 * instance of this class.
 * 
 * @see SingletonLabelFactory
 * 
 * @author mattias ulbrich
 */
public final class SimpleTermLabel implements TermLabel {
   /**
    * Name of {@link #ANON_HEAP_LABEL}.
    */
   public static final Name ANON_HEAP_LABEL_NAME = new Name("anonHeapFunction");

   /**
    * Label attached to anonymisation heap function symbols as for instance
    * introduce in UseOperationContractRule or WhileInvariantRule.
    */
   public static final TermLabel ANON_HEAP_LABEL = new SimpleTermLabel(ANON_HEAP_LABEL_NAME);

   /**
    * Name of {@link #SELECT_SKOLEM_LABEL}.
    */
   public static final Name SELECT_SKOLEM_LABEL_NAME = new Name("selectSK");

   /**
    * Label attached to skolem constants introduced by the rule pullOutSelect.
    */
   public static final TermLabel SELECT_SKOLEM_LABEL = new SimpleTermLabel(SELECT_SKOLEM_LABEL_NAME);

   /**
    * Name of {@link #LOOP_BODY_LABEL}.
    */
   public static final Name LOOP_BODY_LABEL_NAME = new Name("LoopBody");

   /**
    * Label attached to the modality which executes a loop body in branch
    * "Body Preserves Invariant" of applied "Loop Invariant" rules.
    */
   public static final TermLabel LOOP_BODY_LABEL = new SimpleTermLabel(LOOP_BODY_LABEL_NAME);

   /**
    * Name of {@link #LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL}.
    */
   public static final Name LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME = new Name("LoopInvariantNormalBehavior");

   /**
    * Label attached to the implication when a loop body execution terminated
    * normally without any exceptions, returns or breaks in branch
    * "Body Preserves Invariant" of applied "Loop Invariant" rules to show the
    * loop invariant.
    */
   public static final TermLabel LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL = new SimpleTermLabel(LOOP_INVARIANT_NORMAL_BEHAVIOR_LABEL_NAME);

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
    public SimpleTermLabel(Name name) {
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
     * <p>This object is equal to another {@link SimpleTermLabel} iff they
     * bear the same name.
     */
    @Override 
    public boolean equals(Object obj) {
        if (obj instanceof SimpleTermLabel) {
            SimpleTermLabel other = (SimpleTermLabel) obj;
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
