/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import java.util.List;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;

/**
 * This interface describes a commands that manipulate taclets during construction in the parser.
 * <p>
 * Currently, we use this interface to handle the construction of
 * {@link de.uka.ilkd.key.rule.VariableCondition} ({@code \varcond}), but may be used in future for
 * other facilities.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public interface TacletBuilderCommand {
    /**
     * Checks if this command is responsible for the given command name. For example, for
     * {@code \varcond(\newType(t))} the name would be "newType".
     */
    boolean isSuitableFor(@Nonnull String name);

    /**
     * Defines the amount and type of expected arguments. For example, if you want describe a
     * sub-type test (instanceOf) you would need two sorts {@code new ArgumentType[]{SORT,SORT} } as
     * arguments.
     * <p>
     * The parse guarantees, that the types are suitable, when calling
     * {@link #apply(TacletBuilder, Object[], List, boolean)}.
     * </p>
     *
     * @see ArgumentType
     */
    ArgumentType[] getArgumentTypes();

    /**
     * Applying this command on the given taclet builder.
     * <p>
     * During application, this method should alter, e.g., add a
     * {@link de.uka.ilkd.key.rule.VariableCondition}, to the taclet builder.
     * <p>
     * The given arguments are well-typed for supplied {@link #getArgumentTypes()}.
     */
    void apply(TacletBuilder<?> tacletBuilder, Object[] arguments, List<String> parameters,
            boolean negated);
}
