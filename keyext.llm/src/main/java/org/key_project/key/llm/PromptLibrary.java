/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import com.google.gson.GsonBuilder;

import org.jspecify.annotations.Nullable;

/**
 * The file-backed library of user-defined prompts (JSON files in the KeY config directory).
 * <p>
 * {@code @file:} references and {@code $tokens} inside templates are resolved at insertion time;
 * see {@link PromptResolver}.
 *
 * @author Alexander Weigl
 */
public final class PromptLibrary extends FileBackedLibrary<Prompt> {
    public static final PromptLibrary INSTANCE = new PromptLibrary();

    private PromptLibrary() {
    }

    @Override
    protected String subDirectory() {
        return "prompts";
    }

    @Override
    protected Prompt fromJson(String json) {
        try {
            return new GsonBuilder().create().fromJson(json, Prompt.class);
        } catch (Exception e) {
            return null;
        }
    }

    @Override
    protected String toJson(Prompt element) {
        return new GsonBuilder().setPrettyPrinting().create().toJson(element);
    }

    @Override
    protected String nameOf(Prompt element) {
        return element.name();
    }

    @Override
    protected String validate(Prompt element) {
        if (!validName(element.name())) {
            return "Name may only contain letters, digits, '_' and '-'.";
        }
        return null;
    }

    /**
     * Renders a prompt template: resolves markup and returns the text to be inserted into the input
     * box (kept editable), together with a resolved copy for direct messages.
     */
    public static @Nullable Prompt find(String name) {
        return INSTANCE.get(name);
    }
}
