/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser;

import java.util.*;

import org.key_project.logic.Choice;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.rusty.parser.builder.AbstractBuilder;

import org.jspecify.annotations.NonNull;

/**
 * This visitor gathers the choice information in {@link org.key_project.rusty.parser.KeYAst.File}
 * and
 * provide {@link ChoiceInformation}.
 *
 * @author Alexander Weigl
 * @version 1 (28.10.19)
 * @see ChoiceInformation
 */
public class ChoiceFinder extends AbstractBuilder<Object> {
    private final @NonNull ChoiceInformation choiceInformation;

    public ChoiceFinder() {
        choiceInformation = new ChoiceInformation();
    }

    public ChoiceFinder(@NonNull ChoiceInformation choiceInformation) {
        this.choiceInformation = choiceInformation;
    }

    @Override
    public Object visitDecls(org.key_project.rusty.parser.KeYRustyParser.DeclsContext ctx) {
        ctx.option_decls().forEach(this::accept);
        ctx.options_choice().forEach(this::accept);
        return null;
    }

    @Override
    public Object visitChoice(org.key_project.rusty.parser.KeYRustyParser.ChoiceContext ctx) {
        String category = ctx.category.getText();
        List<String> options = new ArrayList<>(ctx.optionDecl().size());
        ctx.optionDecl().forEach(it -> options.add(it.IDENT.getText()));
        if (options.isEmpty()) {
            options.add("on");
            options.add("off");
        }

        seq().put(category, new HashSet<>(options));
        choiceInformation.setDefaultOption(category, options.getFirst());
        options.forEach(it -> choices().add(new Choice(it, category)));
        return null;
    }

    @Override
    public Choice visitActivated_choice(
            org.key_project.rusty.parser.KeYRustyParser.Activated_choiceContext ctx) {
        String cat = ctx.cat.getText();
        String ch = ctx.choice_.getText();
        if (activatedChoicesCategories().contains(cat)) {
            throw new IllegalArgumentException(
                "You have already chosen a different option for " + cat);
        }
        activatedChoicesCategories().add(cat);
        String name = cat + ":" + ch;
        Choice c = choices().lookup(new Name(name));
        if (c == null) {
            c = new Choice(ch, cat);
            choices().add(c);
            // weigl: hit by several test caes:
            // semanticError(ctx, "Choice %s not previously declared", name);
        }
        activatedChoices().add(c);
        return c;
    }

    public @NonNull ChoiceInformation getChoiceInformation() {
        return choiceInformation;
    }

    // region access functions
    private Set<Choice> activatedChoices() {
        return choiceInformation.getActivatedChoices();
    }

    private HashSet<String> activatedChoicesCategories() {
        return choiceInformation.getActivatedChoicesCategories();
    }

    private HashSet<String> options() {
        return choiceInformation.getActivatedChoicesCategories();
    }

    private Namespace<@NonNull Choice> choices() {
        return choiceInformation.getChoices();
    }

    private Map<String, Set<String>> seq() {
        return choiceInformation.getFoundChoicesAndOptions();
    }
    // endregion
}
