/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.nio.file.Path;
import java.util.List;

import org.jspecify.annotations.Nullable;

/**
 * Embedded editor for the user-defined skills ({@link SkillLibrary}) shown in the LLM settings
 * panel. Skills are regular Markdown files: "New" creates a template file with prefilled
 * metadata (front matter with {@code name}, {@code description} and {@code enabled}), "Edit"
 * opens the file in the system editor.
 *
 * @author Alexander Weigl
 */
public class SkillLibraryEditor extends LibraryEditorPanel<Skill> {
    /** Body of the file created by "New". */
    static final String NEW_TEMPLATE =
        "Describe the instructions the agent should follow while this skill is active. Tokens"
            + " such as $seq or $goals can be used.";

    public SkillLibraryEditor() {
        super("Skills",
            "A skill adds focused instructions and an optional tool whitelist to the agent's"
                + " system prompt. The files live in the search path below and can be edited"
                + " with any text editor.");
        reload();
    }

    @Override
    protected List<Skill> loadAll() {
        return SkillLibrary.INSTANCE.all();
    }

    @Override
    protected String nameOf(Skill e) {
        return e.name();
    }

    @Override
    protected String descriptionOf(Skill e) {
        return e.description();
    }

    @Override
    protected String store(Skill e) {
        return SkillLibrary.INSTANCE.save(e);
    }

    @Override
    protected String removeByName(String name) {
        return SkillLibrary.INSTANCE.delete(name);
    }

    @Override
    protected String createEntry(String name) {
        if (SkillLibrary.INSTANCE.exists(name)) {
            return "A skill named '" + name + "' already exists.";
        }
        return SkillLibrary.INSTANCE.save(new Skill(name, "", NEW_TEMPLATE, List.of(), true));
    }

    @Override
    protected @Nullable Path fileOf(String name) {
        return SkillLibrary.INSTANCE.fileOf(name);
    }

    @Override
    protected String toMarkdown(Skill e) {
        return SkillLibrary.serialize(e);
    }

    @Override
    protected @Nullable Skill fromMarkdown(String markdown) {
        return SkillLibrary.parse(markdown);
    }

    @Override
    protected List<String> searchDirs() {
        return LlmSettings.INSTANCE.getSkillLibraryPaths();
    }

    @Override
    protected void setSearchDirs(List<String> dirs) {
        LlmSettings.INSTANCE.setSkillLibraryPaths(dirs);
    }

    @Override
    protected Path defaultDirectory() {
        return SkillLibrary.INSTANCE.defaultDir();
    }
}
