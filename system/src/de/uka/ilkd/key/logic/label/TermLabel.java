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
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelUpdate;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring.RefactoringScope;

/**
 * <p>
 * The interface for term labels. Term labels are annotations that can be attached
 * to {@link Term}s and carry additional information.
 * <b>They must not be soundness relevant</b>. But they may be used in strategies
 * to compute the order in which rules are applied.
 * </p>
 * <p>
 * {@link Term}s with or without term labels are still unmodifiable.
 * It is recommended to implement {@link TermLabel}s including their parameters also unmodifiable.
 * For new {@link TermLabel}s without parameters class {@link ParameterlessTermLabel} can be used.
 * </p>
 * <p>
 * A term label can have parameters accessible via {@link #getChild(int)} and
 * {@link #getChildCount()}. Such parameters can be any {@link Object}.
 * But keep in mind that it is required to parse {@link String}s into {@link Term}s,
 * e.g. if it is used in a Taclet definition or if a cut rule is applied.
 * For convenience parameters are always printed as {@link String}s
 * and have to be parsed individually into the required {@link Object} instances
 * via a {@link TermLabelFactory}.
 * </p>
 * <p>
 * Which {@link TermLabel}s are available is defined by the {@link Profile} or
 * more precise by its {@link TermLabelManager} available via {@link Profile#getTermLabelManager()}.
 * The {@link TermLabelManager} provides also the functionality to parse and maintain them during prove.
 * </p>
 * <p>
 * The {@link TermLabelManager} is responsible during prove to maintain term labels.
 * This means that labels of new {@link Term}s created during rule application are computed
 * via {@link TermLabelManager#instantiateLabels(de.uka.ilkd.key.java.Services, de.uka.ilkd.key.logic.PosInOccurrence, Term, de.uka.ilkd.key.rule.Rule, de.uka.ilkd.key.proof.Goal, Object, Term, de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.collection.ImmutableArray, de.uka.ilkd.key.collection.ImmutableArray, de.uka.ilkd.key.logic.JavaBlock)}
 * and of existing {@link Term}s are refactored (added or removed) via
 * {@link TermLabelManager#refactorLabels(de.uka.ilkd.key.java.Services, de.uka.ilkd.key.logic.PosInOccurrence, Term, de.uka.ilkd.key.rule.Rule, de.uka.ilkd.key.proof.Goal, Term)}.
 * </p>
 * <p>
 * To implement a new {@link TermLabel} follow the following steps:
 * <ol>
 *    <li>
 *       Provide {@link TermLabel} implementation.
 *       <ul>
 *          <li>Without parameters: Add a constant with the {@link Name} and one with the instance to {@link ParameterlessTermLabel}.</li>
 *          <li>With parameters: Implement new class realizing the interface {@link TermLabel}.</li>
 *       </ul>
 *    </li>
 *    <li>
 *       Provide a {@link TermLabelFactory} which will be used during the parse process.
 *       <ul>
 *          <li>Without parameters: Reuse class {@link SingletonLabelFactory} with the instance added as constant to {@link ParameterlessTermLabel}.</li>
 *          <li>With parameters: Implement new class realizing the interface {@link TermLabelFactory}.</li>
 *       </ul>
 *    </li>
 *    <li>
 *       Define how the {@link TermLabel} is maintained during prove.
 *       This may have to be done for different rules in different ways.
 *       Orienteer yourself for each rule on the examples provided in the following.
 *       They are ordered with the less to the most performance impact during prove.
 *       Try to treat as many rules as possible with the same solution, but
 *       <b>choose always the solution with the less performance impact!</b>
 *       <ul>
 *          <li>{@code a(b<<l>>) ~~> c(b<<l>>)}: {@code b} is a constant which is never rewritten by rules. The label stays on the {@link Term} and will be dropped when the {@link Term} is dropped. Nothing to be done.</li>
 *          <li>{@code a ~~> b<<l>>}: The taclet rewrites {@code a} into {@code b<<l>>}. {@link TermLabel}s defined by taclets are automatically considered during rule application. Nothing to be done.</li>
 *          <li>{@code a<<l>> ~~> b<<l>>} The application {@link Term} {@code a} contains the label before. Use an application {@link TermLabelPolicy} to ensure that it is maintained.</li>
 *          <li>{@code Update[...]<<l>> ~~> Update[...new...]<<l>>} The application {@link Term} {@code Update} contains a {@link Modality}. Use a modality {@link TermLabelPolicy} to ensure that it is maintained.</li>
 *          <li>{@code 2 + 3 ~~> 5<>a>>}: A new label has to be added which is not provided by the rule. Implement a {@link TermLabelUpdate} which adds, sorts or removes {@link TermLabel} before a new {@link Term} is created.</li>
 *          <li>{@code 2<<a>> + 3<<b>> ~~> 5<<a>>}: A direct child of the application {@link Term} {@code a} contains the label before. Use a direct {@link ChildTermLabelPolicy} to ensure that it is added also to the new term.</li>
 *          <li>{@code 2 + (3<<a>> - 1<<b>>) ~~> 4<<a>>}: A child or grandchild of the application {@link Term} {@code a} contains the label before. Use a direct {@link ChildTermLabelPolicy} to ensure that it is added also to the new term.</li>
 *          <li>{@code 2<<a>> + 3<<b>> ~~> 2<<a>> - 3}: Implement a {@link TermLabelRefactoring} which works on {@link RefactoringScope#APPLICATION_DIRECT_CHILDREN} to freely add or remove {@link TermLabel}s on direct children of the application {@link Term}.</li>
 *          <li>{@code 2 + (3<<a>> - 1<<b>>) ~~> 2 * (3<<a>> - 1)}: Implement a {@link TermLabelRefactoring} which works on {@link RefactoringScope#APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE} to freely add or remove {@link TermLabel}s on children and grandchildren of the application {@link Term}.</li>
 *          <li>Change labels on the whole {@link Sequent}: Implement a {@link TermLabelRefactoring} which works on {@link RefactoringScope#SEQUENT} to freely add or remove {@link TermLabel}s on any {@link Term} of the {@link Sequent}.</li>
 *       </ul>
 *    </li>
 *    <li>
 *       Make sure that the {@link Profile} supports the new {@link TermLabel}.
 *       All implementations from the previous have to be bundled in a
 *       {@link TermLabelConfiguration} instance. This instance has to be
 *       created and returned in {@link AbstractProfile#computeTermLabelConfiguration()}.
 *    </li>
 *    <li>
 *       During rule application, especially for {@link BuiltInRule}, the
 *       functionality of {@link TermLabelManager} to maintain {@link TermLabel}s
 *       is only called for newly created {@link Term}s labeled up to now. If
 *       your {@link TermLabelPolicy}, {@link TermLabelUpdate} or {@link TermLabelRefactoring}
 *       is not called on the right {@link Term}, it is your task to call
 *       {@link TermLabelManager#instantiateLabels(de.uka.ilkd.key.java.Services, de.uka.ilkd.key.logic.PosInOccurrence, de.uka.ilkd.key.rule.Rule, de.uka.ilkd.key.proof.Goal, Object, Term, de.uka.ilkd.key.logic.op.Operator, de.uka.ilkd.key.collection.ImmutableArray, de.uka.ilkd.key.collection.ImmutableArray, de.uka.ilkd.key.logic.JavaBlock)} and
 *       {@link TermLabelManager#refactorLabels(de.uka.ilkd.key.java.Services, de.uka.ilkd.key.logic.PosInOccurrence, de.uka.ilkd.key.rule.Rule, de.uka.ilkd.key.proof.Goal, Term)}
 *       on the right place in the rule implementation.
 *    </li>
 * </ol>
 * </p>
 * @author Martin Hentschel
 * @see TermLabelManager
 */
public interface TermLabel extends Named {

    /**
     * Retrieves the i-th parameter object of this term label.
     *
     * <p>
     * A term label may have structure, i.e. can be parameterized.
     *
     * @param i
     *            the number of the parameter to retrieve (
     *            {@code 0 <= i < getChildCount()})
     * @return the selected parameter
     * @throw an {@link IndexOutOfBoundsException} if the given parameter number
     *        <tt>i</tt> is negative or greater-or-equal the number of
     *        parameters returned by {@link #getChildCount()}
     */
    public Object getChild(int i);

    /**
     * Gets the number of parameters of this term label.
     *
     * @return the number of parameters (a non-negative number)
     */
    public int getChildCount();
}