/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.nio.file.Path;
import java.util.List;

import org.jspecify.annotations.Nullable;

/**
 * Embedded editor for the user-defined prompts ({@link PromptLibrary}) shown in the LLM settings
 * panel. Prompts are regular Markdown files: "New" creates a template file with prefilled
 * metadata, "Edit" opens the file in the system editor.
 *
 * @author Alexander Weigl
 */
public class PromptLibraryEditor extends LibraryEditorPanel<Prompt> {
    /** Body of the file created by "New". */
    static final String NEW_TEMPLATE =
        "Describe the task for the agent here. Tokens such as $seq or $goals and file"
            + " references like @src/Main.java are resolved at insertion time.";

    public PromptLibraryEditor() {
        super("Prompts",
            "Reusable prompt templates for the chat; insert them with /prompt:NAME. The files"
                + " live in the search path below and can be edited with any text editor.");
        reload();
    }

    @Override
    protected List<Prompt> loadAll() {
        return PromptLibrary.INSTANCE.all();
    }

    @Override
    protected String nameOf(Prompt e) {
        return e.name();
    }

    @Override
    protected String descriptionOf(Prompt e) {
        return e.description();
    }

    @Override
    protected String store(Prompt e) {
        return PromptLibrary.INSTANCE.save(e);
    }

    @Override
    protected String removeByName(String name) {
        return PromptLibrary.INSTANCE.delete(name);
    }

    @Override
    protected String createEntry(String name) {
        if (PromptLibrary.INSTANCE.exists(name)) {
            return "A prompt named '" + name + "' already exists.";
        }
        return PromptLibrary.INSTANCE.save(new Prompt(name, "", NEW_TEMPLATE));
    }

    @Override
    protected @Nullable Path fileOf(String name) {
        return PromptLibrary.INSTANCE.fileOf(name);
    }

    @Override
    protected String toMarkdown(Prompt e) {
        return PromptLibrary.serialize(e);
    }

    @Override
    protected @Nullable Prompt fromMarkdown(String markdown) {
        return PromptLibrary.parse(markdown);
    }

    @Override
    protected List<String> searchDirs() {
        return LlmSettings.INSTANCE.getPromptLibraryPaths();
    }

    @Override
    protected void setSearchDirs(List<String> dirs) {
        LlmSettings.INSTANCE.setPromptLibraryPaths(dirs);
    }

    @Override
    protected Path defaultDirectory() {
        return PromptLibrary.INSTANCE.defaultDir();
    }
}
