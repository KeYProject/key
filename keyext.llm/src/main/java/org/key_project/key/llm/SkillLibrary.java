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
 * The file-backed library of user-defined skills (Markdown files with a YAML front matter in the
 * KeY config directory). An active skill is selected on the {@link LlmSession}; its instructions
 * are appended to the system prompt and its {@code allowedTools} whitelist narrows the advertised
 * tool set.
 *
 * @author Alexander Weigl
 */
public final class SkillLibrary extends FileBackedLibrary<Skill> {
    public static final SkillLibrary INSTANCE = new SkillLibrary();

    private SkillLibrary() {
    }

    // ------------------------------------------------------------- FileBackedLibrary hooks

    @Override
    protected String subDirectory() {
        return "skills";
    }

    @Override
    protected List<String> configuredSearchPath() {
        return LlmSettings.INSTANCE.getSkillLibraryPaths();
    }

    @Override
    protected @Nullable Skill fromMarkdown(String markdown) {
        return parse(markdown);
    }

    @Override
    protected String toMarkdown(Skill element) {
        return serialize(element);
    }

    @Override
    protected @Nullable Skill fromLegacyJson(String json) {
        try {
            return new GsonBuilder().create().fromJson(json, Skill.class);
        } catch (Exception e) {
            return null;
        }
    }

    @Override
    protected String nameOf(Skill element) {
        return element.name();
    }

    @Override
    protected String validate(Skill element) {
        if (!validName(element.name())) {
            return "Name may only contain letters, digits, '_' and '-'.";
        }
        return null;
    }

    // ------------------------------------------------- public Markdown format (used by the editor)

    /**
     * Parses a skill from its Markdown document (YAML front matter: {@code name},
     * {@code description}, {@code enabled}, optional {@code allowedTools}; body: the
     * instructions). Returns {@code null} when the document has no usable front matter or a blank
     * name.
     */
    public static @Nullable Skill parse(String markdown) {
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
        boolean enabled = meta.get("enabled") instanceof Boolean b ? b : true;
        var allowedTools = MarkdownFrontMatter.stringList(meta, "allowedTools");
        return new Skill(name, description, parsed.body(), allowedTools, enabled);
    }

    /** Serializes a skill to its Markdown document. */
    public static String serialize(Skill skill) {
        var meta = new LinkedHashMap<String, Object>();
        meta.put("name", skill.name());
        meta.put("description", skill.description());
        meta.put("enabled", skill.enabled());
        if (!skill.allowedTools().isEmpty()) {
            meta.put("allowedTools", skill.allowedTools());
        }
        return MarkdownFrontMatter.render(meta, skill.instructions());
    }
}
