/**
 * contains the operators of {@link
 * de.uka.ilkd.key.logic.Term}s. Operators may be {@link
 * de.uka.ilkd.key.logic.op.Quantifier}s or {@link
 * de.uka.ilkd.key.logic.op.SubstOp}s that bind variables for
 * subterms, but also {@link de.uka.ilkd.key.logic.op.Modality}s. Many of the operators
 * are constantly defined in {@link de.uka.ilkd.key.logic.op.Junctor}s.
 * An operator can be a {@link de.uka.ilkd.key.logic.op.AbstractSortedOperator}s,
 * such as a {@link de.uka.ilkd.key.logic.op.JFunction} or a
 * variable. There are several kind of variables: {@link
 * de.uka.ilkd.key.logic.op.LogicVariable}s (variables that must be
 * bound but do not occur in programs), {@link
 * de.uka.ilkd.key.logic.op.ProgramVariable}s (allowed both in
 * programs and in logic, but not boundable) and {@link
 * de.uka.ilkd.key.logic.op.OperatorSV}s for {@link
 * de.uka.ilkd.key.rule.Taclet}s.
 */
package de.uka.ilkd.key.logic.op;
