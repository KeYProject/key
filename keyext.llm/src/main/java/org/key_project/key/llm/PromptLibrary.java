/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.util.LinkedHashMap;
import java.util.List;

import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;

/**
 * The file-backed library of user-defined prompts (Markdown files with a YAML front matter in the
 * KeY config directory).
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

    // ------------------------------------------------------------- FileBackedLibrary hooks

    @Override
    protected String subDirectory() {
        return "prompts";
    }

    @Override
    protected List<String> configuredSearchPath() {
        return LlmSettings.INSTANCE.getPromptLibraryPaths();
    }

    @Override
    protected @Nullable Prompt fromMarkdown(String markdown) {
        return parse(markdown);
    }

    @Override
    protected String toMarkdown(Prompt element) {
        return serialize(element);
    }

    @Override
    protected @Nullable Prompt fromLegacyJson(String json) {
        try {
            return new GsonBuilder().create().fromJson(json, Prompt.class);
        } catch (Exception e) {
            return null;
        }
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

    // ------------------------------------------------- public Markdown format (used by the editor)

    /**
     * Parses a prompt from its Markdown document (YAML front matter: {@code name},
     * {@code description}; body: the template). Returns {@code null} when the document has no
     * usable front matter or a blank name.
     */
    public static @Nullable Prompt parse(String markdown) {
        var parsed = MarkdownFrontMatter.parse(markdown);
        if (parsed == null) {
            return null;
        }
        var meta = parsed.meta();
        var name = MarkdownFrontMatter.stringValue(meta, "name");
        if (name == null || name.isBlank()) {
            return null;
        }
        var description = MarkdownFrontMatter.stringValue(meta, "description");
        return new Prompt(name, description, parsed.body());
    }

    /** Serializes a prompt to its Markdown document. */
    public static String serialize(Prompt prompt) {
        var meta = new LinkedHashMap<String, Object>();
        meta.put("name", prompt.name());
        meta.put("description", prompt.description());
        return MarkdownFrontMatter.render(meta, prompt.template());
    }

    /**
     * Renders a prompt template: resolves markup and returns the text to be inserted into the input
     * box (kept editable), together with a resolved copy for direct messages.
     */
    public static @Nullable Prompt find(String name) {
        return INSTANCE.get(name);
    }
}
